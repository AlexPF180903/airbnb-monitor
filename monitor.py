#!/usr/bin/env python3
"""Monitor de disponibilidad de Airbnb con alertas por Telegram.

Códigos de salida:
    0 -> ejecución correcta (haya o no disponibilidad).
    1 -> fallo persistente de carga/detección o fallo al enviar a Telegram.
    2 -> error de configuración.
"""

from __future__ import annotations

import argparse
import html
import json
import logging
import os
import re
import sys
import time
import unicodedata
from dataclasses import dataclass
from datetime import date, datetime, timezone
from enum import Enum
from pathlib import Path
from typing import Optional, Tuple

import requests
from dotenv import load_dotenv
from playwright.sync_api import Error as PlaywrightError
from playwright.sync_api import Locator, Page, sync_playwright

LOG = logging.getLogger("airbnb_monitor")

# --------------------------------------------------------------------------- #
# Valores por defecto
# --------------------------------------------------------------------------- #
DEFAULT_ROOM_ID = "10491212"
DEFAULT_CHECK_IN = "2026-10-30"
DEFAULT_CHECK_OUT = "2026-11-02"
DEFAULT_ADULTS = "3"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)
VIEWPORT = {"width": 1366, "height": 768}
EXTRA_HEADERS = {
    "Accept-Language": "es-MX,es;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept": (
        "text/html,application/xhtml+xml,application/xml;q=0.9,"
        "image/avif,image/webp,image/apng,*/*;q=0.8"
    ),
    "Upgrade-Insecure-Requests": "1",
    "sec-ch-ua": '"Chromium";v="131", "Not_A Brand";v="24", "Google Chrome";v="131"',
    "sec-ch-ua-mobile": "?0",
    "sec-ch-ua-platform": '"Windows"',
}
STEALTH_JS = """
Object.defineProperty(navigator, 'webdriver', { get: () => false });
Object.defineProperty(navigator, 'languages', { get: () => ['es-MX', 'es', 'en-US', 'en'] });
Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
window.chrome = window.chrome || { runtime: {} };
const originalQuery = window.navigator.permissions && window.navigator.permissions.query;
if (originalQuery) {
  window.navigator.permissions.query = (parameters) => (
    parameters && parameters.name === 'notifications'
      ? Promise.resolve({ state: Notification.permission })
      : originalQuery(parameters)
  );
}
"""

PANEL_SELECTORS = (
    '[data-section-id="BOOK_IT_SIDEBAR"]',
    '[data-plugin-in-point-id="BOOK_IT_SIDEBAR"]',
    '[data-section-id="BOOK_IT_FLOATING_FOOTER"]',
)
CTA_TESTID_SELECTOR = 'button[data-testid="homes-pdp-cta-btn"]'

RESERVE_RE = re.compile(r"^\s*(Reservar|Reserve)\s*$", re.IGNORECASE)
CHECK_RE = re.compile(
    r"^\s*(Verificar disponibilidad|Check availability)\s*$", re.IGNORECASE
)

# Se comparan contra texto normalizado (minúsculas y sin acentos).
UNAVAILABLE_MARKERS = (
    "no estan disponibles",
    "no esta disponible",
    "no disponible",
    "fechas no disponibles",
    "no hay disponibilidad",
    "estancia minima",
    "not available",
    "arent available",
    "unavailable",
    "minimum stay",
)
BLOCK_MARKERS = (
    "access denied",
    "captcha",
    "unusual traffic",
    "verifica que eres humano",
    "are you a human",
    "pardon our interruption",
    "request blocked",
)
AMOUNT_RE = re.compile(r"(?:[A-Z]{2,3})?\s?\$\s?\d[\d.,]*(?:\s?[A-Z]{3})?")

POLL_TIMEOUT_S = 40
POLL_INTERVAL_MS = 3000
CONFIRMATIONS_REQUIRED = 2


# --------------------------------------------------------------------------- #
# Excepciones y modelos
# --------------------------------------------------------------------------- #
class ConfigError(Exception):
    """Configuración inválida o incompleta."""


class FatalError(Exception):
    """Error no recuperable (no tiene sentido reintentar)."""


class RetryableError(Exception):
    """Error transitorio: se reintenta."""


class BlockedError(RetryableError):
    """Airbnb mostró una página anti-bot / captcha."""


class IndeterminateError(RetryableError):
    """No se pudo determinar el estado de disponibilidad."""


class TelegramError(Exception):
    """Fallo al enviar el mensaje a Telegram."""


class Status(str, Enum):
    AVAILABLE = "available"
    UNAVAILABLE = "unavailable"
    INDETERMINATE = "indeterminate"


@dataclass(frozen=True)
class CheckResult:
    status: Status
    title: str
    total: Optional[str]
    button: Optional[str]
    detail: str


@dataclass(frozen=True)
class Config:
    room_id: str
    check_in: date
    check_out: date
    adults: int
    bot_token: str
    chat_id: str
    max_retries: int
    timeout_ms: int
    headless: bool
    check_button_counts: bool
    notify_every_run: bool
    state_file: Path
    artifacts_dir: Path

    @property
    def nights(self) -> int:
        return (self.check_out - self.check_in).days

    @property
    def url(self) -> str:
        return (
            f"https://www.airbnb.mx/rooms/{self.room_id}"
            f"?check_in={self.check_in.isoformat()}"
            f"&check_out={self.check_out.isoformat()}"
            f"&adults={self.adults}"
        )

    @classmethod
    def from_env(cls) -> "Config":
        load_dotenv()

        room_id = _env("ROOM_ID", DEFAULT_ROOM_ID)
        if not room_id.isdigit():
            raise ConfigError(f"ROOM_ID debe ser numérico, recibido: {room_id!r}")

        try:
            check_in = date.fromisoformat(_env("CHECK_IN", DEFAULT_CHECK_IN))
            check_out = date.fromisoformat(_env("CHECK_OUT", DEFAULT_CHECK_OUT))
        except ValueError as exc:
            raise ConfigError(f"Fecha inválida (usa YYYY-MM-DD): {exc}") from exc
        if check_out <= check_in:
            raise ConfigError("CHECK_OUT debe ser posterior a CHECK_IN.")

        try:
            adults = int(_env("ADULTS", DEFAULT_ADULTS))
            max_retries = int(_env("MAX_RETRIES", "3"))
            timeout_ms = int(_env("NAV_TIMEOUT_MS", "60000"))
        except ValueError as exc:
            raise ConfigError(f"Valor numérico inválido: {exc}") from exc
        if adults < 1 or max_retries < 1 or timeout_ms < 1000:
            raise ConfigError("ADULTS/MAX_RETRIES/NAV_TIMEOUT_MS tienen valores fuera de rango.")

        return cls(
            room_id=room_id,
            check_in=check_in,
            check_out=check_out,
            adults=adults,
            bot_token=_env("TELEGRAM_BOT_TOKEN", ""),
            chat_id=_env("TELEGRAM_CHAT_ID", ""),
            max_retries=max_retries,
            timeout_ms=timeout_ms,
            headless=_env_bool("HEADLESS", True),
            check_button_counts=_env_bool("CHECK_BUTTON_COUNTS", True),
            notify_every_run=_env_bool("NOTIFY_EVERY_RUN", False),
            state_file=Path(_env("STATE_FILE", ".state/last_status.json")),
            artifacts_dir=Path(_env("ARTIFACTS_DIR", "artifacts")),
        )


def _env(name: str, default: str) -> str:
    """Lee una variable de entorno; vacía o ausente -> default."""
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return value.strip()


def _env_bool(name: str, default: bool) -> bool:
    raw = _env(name, "true" if default else "false").lower()
    return raw in {"1", "true", "yes", "si", "sí", "on"}


# --------------------------------------------------------------------------- #
# Utilidades
# --------------------------------------------------------------------------- #
def _norm(text: str) -> str:
    """Minúsculas, sin acentos y con apóstrofes unificados."""
    text = text.replace("\u2019", "").replace("'", "")
    decomposed = unicodedata.normalize("NFKD", text)
    stripped = "".join(ch for ch in decomposed if not unicodedata.combining(ch))
    return " ".join(stripped.lower().split())


def _redact(text: str, *secrets: str) -> str:
    for secret in secrets:
        if secret:
            text = text.replace(secret, "***")
    return text


def _setup_logging() -> None:
    logging.basicConfig(
        level=os.getenv("LOG_LEVEL", "INFO").upper(),
        format="%(asctime)s | %(levelname)-7s | %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
        stream=sys.stdout,
    )


# --------------------------------------------------------------------------- #
# Telegram
# --------------------------------------------------------------------------- #
def send_telegram(cfg: Config, text: str, button_url: Optional[str] = None) -> None:
    if not cfg.bot_token or not cfg.chat_id:
        raise ConfigError("Faltan TELEGRAM_BOT_TOKEN y/o TELEGRAM_CHAT_ID.")

    endpoint = f"https://api.telegram.org/bot{cfg.bot_token}/sendMessage"
    payload: dict = {
        "chat_id": cfg.chat_id,
        "text": text,
        "parse_mode": "HTML",
    }
    if button_url:
        payload["reply_markup"] = {
            "inline_keyboard": [[{"text": "Abrir en Airbnb", "url": button_url}]]
        }

    last_error = "sin detalle"
    for attempt in range(1, 4):
        try:
            response = requests.post(endpoint, json=payload, timeout=20)
        except requests.RequestException as exc:
            last_error = _redact(str(exc), cfg.bot_token)
            LOG.warning("Telegram: error de red (intento %d/3): %s", attempt, last_error)
            time.sleep(2 * attempt)
            continue

        if response.status_code == 200:
            LOG.info("Mensaje de Telegram enviado correctamente.")
            return

        try:
            body = response.json()
        except ValueError:
            body = {}
        description = body.get("description", response.text[:200])
        last_error = f"HTTP {response.status_code}: {description}"

        if response.status_code == 429:
            wait = int(body.get("parameters", {}).get("retry_after", 5))
            LOG.warning("Telegram: límite de tasa, esperando %ds.", min(wait, 60))
            time.sleep(min(wait, 60))
            continue
        if 400 <= response.status_code < 500:
            raise TelegramError(_redact(last_error, cfg.bot_token))

        LOG.warning("Telegram: error del servidor (intento %d/3): %s", attempt, last_error)
        time.sleep(2 * attempt)

    raise TelegramError(f"No se pudo enviar el mensaje tras 3 intentos. Último error: {last_error}")


def build_availability_message(cfg: Config, result: CheckResult) -> str:
    total = html.escape(result.total) if result.total else "no detectado"
    button = html.escape(result.button or "desconocido")
    lines = [
        "🟢 <b>¡Fechas disponibles en Airbnb!</b>",
        "",
        f"🏠 <b>{html.escape(result.title)}</b>",
        (
            f"📅 {cfg.check_in.strftime('%d/%m/%Y')} → "
            f"{cfg.check_out.strftime('%d/%m/%Y')} ({cfg.nights} noches)"
        ),
        f"👥 Adultos: {cfg.adults}",
        f"💰 Total estimado: {total}",
        f"🔘 Botón detectado: {button}",
        "",
        f'🔗 <a href="{html.escape(cfg.url, quote=True)}">Reservar ahora</a>',
        "",
        "<i>Confirma en Airbnb: otras personas también pueden estar viéndolo.</i>",
    ]
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Estado persistente (evita alertas repetidas cada hora)
# --------------------------------------------------------------------------- #
def load_previous_status(path: Path) -> Optional[str]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        value = data.get("status")
        return value if isinstance(value, str) else None
    except (OSError, ValueError):
        return None


def save_status(path: Path, status: Status) -> None:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "status": status.value,
            "updated_at": datetime.now(timezone.utc).isoformat(),
        }
        path.write_text(json.dumps(payload), encoding="utf-8")
    except OSError as exc:
        LOG.warning("No se pudo guardar el estado en %s: %s", path, exc)


# --------------------------------------------------------------------------- #
# Análisis de la página
# --------------------------------------------------------------------------- #
def _booking_panel(page: Page) -> Tuple[Locator, str]:
    """Devuelve el panel de reserva (o el body como respaldo) y su texto."""
    for selector in PANEL_SELECTORS:
        locator = page.locator(selector).first
        try:
            if locator.count() > 0 and locator.is_visible():
                text = locator.inner_text(timeout=3000)
                if text.strip():
                    return locator, text
        except PlaywrightError:
            continue
    body = page.locator("body")
    return body, body.inner_text(timeout=5000)


def _any_enabled(candidates: Locator) -> bool:
    try:
        total = candidates.count()
    except PlaywrightError:
        return False
    for index in range(total):
        item = candidates.nth(index)
        try:
            if not item.is_visible() or not item.is_enabled():
                continue
            if (item.get_attribute("aria-disabled") or "").lower() == "true":
                continue
            if item.get_attribute("disabled") is not None:
                continue
            return True
        except PlaywrightError:
            continue
    return False


def _has_enabled_button(scope: Locator, pattern: re.Pattern) -> bool:
    by_role = scope.get_by_role("button", name=pattern)
    by_testid = scope.locator(CTA_TESTID_SELECTOR).filter(has_text=pattern)
    return _any_enabled(by_role) or _any_enabled(by_testid)


def _extract_title(page: Page, room_id: str) -> str:
    getters = (
        lambda: page.locator("h1").first.inner_text(timeout=3000),
        lambda: page.locator('meta[property="og:title"]').first.get_attribute(
            "content", timeout=3000
        ),
        page.title,
    )
    for getter in getters:
        try:
            value = getter()
        except PlaywrightError:
            continue
        if value and value.strip():
            return " ".join(value.split())
    return f"Alojamiento {room_id}"


def _extract_total(text: str) -> Optional[str]:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    found: Optional[str] = None
    for index, line in enumerate(lines):
        if not line.lower().startswith("total"):
            continue
        for candidate in lines[index : index + 3]:
            match = AMOUNT_RE.search(candidate)
            if match:
                found = " ".join(match.group(0).split())
                break
    return found


def _guard_against_block(page: Page) -> None:
    title = _norm(page.title() or "")
    if any(marker in title for marker in BLOCK_MARKERS):
        raise BlockedError(f"Página anti-bot detectada (título: {title!r}).")
    try:
        body = _norm(page.locator("body").inner_text(timeout=3000))
    except PlaywrightError:
        return
    if len(body) < 3000 and any(marker in body for marker in BLOCK_MARKERS):
        raise BlockedError("Página anti-bot/captcha detectada en el contenido.")


def analyze_page(page: Page, cfg: Config) -> CheckResult:
    scope, text = _booking_panel(page)
    normalized = _norm(text)
    title = _extract_title(page, cfg.room_id)
    total = _extract_total(text)

    for marker in UNAVAILABLE_MARKERS:
        if marker in normalized:
            return CheckResult(
                Status.UNAVAILABLE, title, total, None, f"mensaje detectado: {marker!r}"
            )

    if _has_enabled_button(scope, RESERVE_RE):
        return CheckResult(Status.AVAILABLE, title, total, "Reservar", "botón Reservar habilitado")

    if cfg.check_button_counts and _has_enabled_button(scope, CHECK_RE):
        return CheckResult(
            Status.AVAILABLE,
            title,
            total,
            "Verificar disponibilidad",
            "botón Verificar disponibilidad habilitado (confirma manualmente)",
        )

    return CheckResult(
        Status.INDETERMINATE, title, total, None, "no se encontró botón ni mensaje de bloqueo"
    )


def _evaluate_with_polling(page: Page, cfg: Config) -> CheckResult:
    """Sondea hasta obtener el mismo estado definitivo dos veces seguidas."""
    deadline = time.monotonic() + POLL_TIMEOUT_S
    confirmations = 0
    previous: Optional[CheckResult] = None
    last: Optional[CheckResult] = None

    while True:
        _guard_against_block(page)
        result = analyze_page(page, cfg)
        last = result
        LOG.debug("Sondeo: %s (%s)", result.status.value, result.detail)

        if result.status is Status.INDETERMINATE:
            previous, confirmations = None, 0
        elif previous is not None and previous.status is result.status:
            confirmations += 1
            if confirmations + 1 >= CONFIRMATIONS_REQUIRED:
                return result
        else:
            previous, confirmations = result, 0

        if time.monotonic() >= deadline:
            return last
        page.wait_for_timeout(POLL_INTERVAL_MS)


def _dismiss_overlays(page: Page) -> None:
    try:
        page.keyboard.press("Escape")
        cookie_btn = page.locator(
            '[data-testid="main-cookies-banner-container"] button'
        ).filter(has_text=re.compile(r"Aceptar|Accept", re.IGNORECASE))
        if cookie_btn.count() > 0 and cookie_btn.first.is_visible():
            cookie_btn.first.click(timeout=3000)
    except PlaywrightError:
        pass


def _save_debug(page: Optional[Page], cfg: Config, tag: str) -> None:
    if page is None:
        return
    try:
        cfg.artifacts_dir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = cfg.artifacts_dir / f"{stamp}_{tag}"
        page.screenshot(path=str(base.with_suffix(".png")), full_page=False)
        base.with_suffix(".txt").write_text(
            page.locator("body").inner_text(timeout=3000), encoding="utf-8"
        )
        LOG.info("Evidencia de depuración guardada en %s.*", base)
    except Exception as exc:  # noqa: BLE001 - la depuración nunca debe romper el flujo
        LOG.warning("No se pudo guardar evidencia de depuración: %s", exc)


# --------------------------------------------------------------------------- #
# Ejecución con Playwright
# --------------------------------------------------------------------------- #
def check_once(cfg: Config) -> CheckResult:
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(
            headless=cfg.headless,
            args=[
                "--disable-blink-features=AutomationControlled",
                "--no-sandbox",
                "--disable-dev-shm-usage",
            ],
        )
        page: Optional[Page] = None
        try:
            context = browser.new_context(
                user_agent=USER_AGENT,
                viewport=VIEWPORT,
                locale="es-MX",
                timezone_id="America/Mexico_City",
                extra_http_headers=EXTRA_HEADERS,
                java_script_enabled=True,
            )
            context.add_init_script(STEALTH_JS)
            page = context.new_page()
            page.set_default_timeout(cfg.timeout_ms)

            LOG.info("Cargando %s", cfg.url)
            response = page.goto(cfg.url, wait_until="domcontentloaded", timeout=cfg.timeout_ms)
            if response is not None:
                status_code = response.status
                if status_code == 404:
                    raise FatalError("El alojamiento no existe o fue retirado (HTTP 404).")
                if status_code >= 400:
                    raise RetryableError(f"Airbnb respondió HTTP {status_code}.")

            try:
                page.wait_for_load_state("networkidle", timeout=15000)
            except PlaywrightError:
                LOG.debug("networkidle no alcanzado; se continúa con el sondeo.")

            _dismiss_overlays(page)
            result = _evaluate_with_polling(page, cfg)
            if result.status is Status.INDETERMINATE:
                _save_debug(page, cfg, "indeterminate")
            return result
        except Exception:
            _save_debug(page, cfg, "error")
            raise
        finally:
            browser.close()


def run_check_with_retries(cfg: Config) -> CheckResult:
    last_error: Optional[BaseException] = None
    for attempt in range(1, cfg.max_retries + 1):
        LOG.info("Intento %d/%d", attempt, cfg.max_retries)
        try:
            result = check_once(cfg)
            if result.status is Status.INDETERMINATE:
                raise IndeterminateError(result.detail)
            return result
        except FatalError:
            raise
        except (PlaywrightError, RetryableError) as exc:
            last_error = exc
            LOG.warning("Fallo en el intento %d: %s", attempt, exc)
            if attempt < cfg.max_retries:
                wait = 10 * attempt
                LOG.info("Reintentando en %ds...", wait)
                time.sleep(wait)
    raise RetryableError(f"Todos los intentos fallaron. Último error: {last_error}")


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def parse_args(argv: Optional[list] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Monitor de disponibilidad de Airbnb.")
    parser.add_argument(
        "--test-telegram",
        action="store_true",
        help="Envía un mensaje de prueba a Telegram y termina.",
    )
    parser.add_argument(
        "--headed",
        action="store_true",
        help="Abre el navegador con interfaz (útil para depurar en local).",
    )
    parser.add_argument(
        "--force-notify",
        action="store_true",
        help="Envía la alerta aunque ya se hubiera notificado antes.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[list] = None) -> int:
    _setup_logging()
    args = parse_args(argv)

    try:
        cfg = Config.from_env()
    except ConfigError as exc:
        LOG.error("Configuración inválida: %s", exc)
        return 2

    if args.headed:
        cfg = Config(**{**cfg.__dict__, "headless": False})
    if args.force_notify:
        cfg = Config(**{**cfg.__dict__, "notify_every_run": True})

    LOG.info(
        "Monitor iniciado | room=%s | %s → %s (%d noches) | adultos=%d",
        cfg.room_id,
        cfg.check_in,
        cfg.check_out,
        cfg.nights,
        cfg.adults,
    )

    if args.test_telegram:
        try:
            send_telegram(
                cfg,
                "✅ <b>Prueba del monitor de Airbnb</b>\nLa conexión con Telegram funciona.",
                button_url=cfg.url,
            )
            return 0
        except (ConfigError, TelegramError) as exc:
            LOG.error("Prueba de Telegram fallida: %s", exc)
            return 1

    try:
        result = run_check_with_retries(cfg)
    except FatalError as exc:
        LOG.error("Error fatal: %s", exc)
        return 1
    except RetryableError as exc:
        LOG.error("No se pudo completar la verificación: %s", exc)
        return 1

    LOG.info("Resultado: %s | %s | título=%s", result.status.value, result.detail, result.title)

    if result.status is Status.UNAVAILABLE:
        LOG.info("Sin disponibilidad para las fechas solicitadas.")
        save_status(cfg.state_file, Status.UNAVAILABLE)
        return 0

    previous = load_previous_status(cfg.state_file)
    if previous == Status.AVAILABLE.value and not cfg.notify_every_run:
        LOG.info("Sigue disponible, pero ya se notificó en una ejecución anterior.")
        return 0

    try:
        send_telegram(cfg, build_availability_message(cfg, result), button_url=cfg.url)
    except (ConfigError, TelegramError) as exc:
        LOG.error("No se pudo enviar la alerta: %s", exc)
        return 1

    save_status(cfg.state_file, Status.AVAILABLE)
    return 0


if __name__ == "__main__":
    sys.exit(main())
