"""
Telegram bot: direct download link -> split into parts -> GitHub Release.

Flow:
  1. You send the bot a *direct download link* (the temporary CDN link Nexus
     gives you after "Slow download"), NOT the mod page link.
  2. The bot downloads the file part by part (CHUNK_SIZE_MB each) onto a
     temporary disk file, uploads every part to a GitHub Release, deletes it
     from disk and sends you a Telegram message with the part's download link.
  3. Network errors are retried automatically (downloads resume from the exact
     byte where they broke, uploads are re-sent).
"""
from __future__ import annotations

import asyncio
import errno
import html
import logging
import math
import os
import re
import shutil
import string
import time
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlparse

import aiohttp
from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart
from aiogram.types import Message

try:  # optional: load a local .env file when running on your own machine
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

# --------------------------------------------------------------------------- #
# Config (environment variables)
# --------------------------------------------------------------------------- #
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN", "")
GITHUB_OWNER = os.getenv("GITHUB_OWNER", "")
GITHUB_REPO = os.getenv("GITHUB_REPO", "")
GITHUB_API = os.getenv("GITHUB_API_URL", "https://api.github.com").rstrip("/")

# GitHub allows < 2 GiB per release asset, so never go above 2000 MB.
CHUNK_SIZE = int(min(float(os.getenv("CHUNK_SIZE_MB", "1900")), 2000) * 1024 * 1024)
MAX_RETRIES = int(os.getenv("MAX_RETRIES", "5"))
WORK_DIR = Path(os.getenv("WORK_DIR", "/tmp/nexus_bot"))
ALLOWED_USERS = {
    int(x) for x in re.split(r"[,\s]+", os.getenv("ALLOWED_USER_IDS", "")) if x.isdigit()
}

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36"
)
URL_RE = re.compile(r"https?://\S+")
STATUS_EDIT_INTERVAL = 5  # seconds between edits of the progress message

logging.basicConfig(
    level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s"
)
log = logging.getLogger("nexus-bot")


# --------------------------------------------------------------------------- #
# Errors + small helpers
# --------------------------------------------------------------------------- #
class BotError(Exception):
    """Fatal error with a message that is safe to show to the user."""


class Transient(Exception):
    """Temporary problem (5xx, 429, early disconnect...) -> worth retrying."""


RETRYABLE = (aiohttp.ClientError, asyncio.TimeoutError, ConnectionError, Transient)


def fmt_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.2f} {unit}"
        n /= 1024
    return f"{n:.2f} GB"


def fmt_duration(seconds: float) -> str:
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h {m:02d}m" if h else f"{m}m {s:02d}s"


def part_suffix(i: int) -> str:
    """0 -> 'aa', 1 -> 'ab', ... (same as `split`, so `cat name.part_*` works)."""
    if i >= 26 * 26:
        raise BotError("تعداد پارت‌ها بیش از حد شد؛ CHUNK_SIZE_MB رو بیشتر کن.")
    return string.ascii_lowercase[i // 26] + string.ascii_lowercase[i % 26]


def safe_name(name: str) -> str:
    name = re.sub(r"[^A-Za-z0-9._-]+", "_", name).strip("._")
    return (name or "download.bin")[:150]


def short_err(e: BaseException) -> str:
    return f"{type(e).__name__}: {e}"[:120]


def looks_like_mod_page(url: str) -> bool:
    """nexusmods.com / www.nexusmods.com are web pages; the CDN hosts are subdomains."""
    host = (urlparse(url).hostname or "").lower()
    return host in ("nexusmods.com", "www.nexusmods.com")


async def with_retry(fn, describe: str, notify):
    """Run `await fn()`; retry retryable errors with exponential backoff."""
    attempt = 0
    while True:
        try:
            return await fn()
        except RETRYABLE as e:
            attempt += 1
            if attempt > MAX_RETRIES:
                raise BotError(
                    f"{describe} بعد از {MAX_RETRIES} بار تلاش ناموفق بود ({short_err(e)})."
                ) from e
            delay = min(60, 2**attempt)
            log.warning("%s failed (%s); retry %d/%d in %ds", describe, e, attempt, MAX_RETRIES, delay)
            await notify(
                f"⚠️ {describe}: خطا ({short_err(e)})\n"
                f"🔁 تلاش مجدد {attempt}/{MAX_RETRIES} تا {delay} ثانیه‌ی دیگه..."
            )
            await asyncio.sleep(delay)


# --------------------------------------------------------------------------- #
# Telegram helpers
# --------------------------------------------------------------------------- #
async def send(bot: Bot, chat_id: int, text: str) -> Message | None:
    """Send a message; never let a Telegram hiccup kill the job."""
    try:
        return await bot.send_message(chat_id, text)
    except Exception as e:  # noqa: BLE001
        log.warning("send_message failed: %s", e)
        return None


class Status:
    """One message that is edited in place to show live progress."""

    def __init__(self, bot: Bot, chat_id: int):
        self.bot, self.chat_id = bot, chat_id
        self.msg: Message | None = None
        self.text = ""
        self.last = 0.0

    def due(self) -> bool:
        return time.monotonic() - self.last >= STATUS_EDIT_INTERVAL

    async def set(self, text: str, force: bool = False) -> None:
        if text == self.text or not (force or self.due()):
            return
        self.text = text
        self.last = time.monotonic()
        try:
            if self.msg is None:
                self.msg = await self.bot.send_message(self.chat_id, text)
            else:
                await self.msg.edit_text(text)
        except Exception as e:  # noqa: BLE001
            log.warning("status update failed: %s", e)


# --------------------------------------------------------------------------- #
# Download side: one long connection, reconnects (with Range) on failure
# --------------------------------------------------------------------------- #
class Source:
    def __init__(self, session: aiohttp.ClientSession, url: str, notify):
        self.session, self.url, self.notify = session, url, notify
        self.resp: aiohttp.ClientResponse | None = None
        self.pos = 0  # bytes of the *whole file* consumed so far
        self.total: int | None = None
        self.filename: str | None = None

    async def connect(self) -> None:
        await with_retry(self._open, "اتصال به لینک دانلود", self.notify)

    def close(self) -> None:
        if self.resp is not None:
            self.resp.close()
            self.resp = None

    async def _open(self) -> None:
        self.close()
        headers = {"User-Agent": USER_AGENT, "Accept-Encoding": "identity"}
        if self.pos:
            headers["Range"] = f"bytes={self.pos}-"
        resp = await self.session.get(self.url, headers=headers)
        try:
            self._check(resp)
        except BaseException:
            resp.close()
            raise
        self.resp = resp
        if self.filename is None:
            self._learn(resp)

    def _check(self, resp: aiohttp.ClientResponse) -> None:
        s = resp.status
        if s in (401, 403, 410):
            raise BotError(
                f"لینک دانلود دیگه معتبر نیست (HTTP {s}) — احتمالاً منقضی شده. "
                "یک لینک تازه بگیر و سریع بفرست."
            )
        if s == 404:
            raise BotError("لینک پیدا نشد (HTTP 404).")
        if s == 429 or s >= 500:
            raise Transient(f"HTTP {s}")
        if s not in (200, 206):
            raise BotError(f"پاسخ غیرمنتظره از سرور (HTTP {s}).")
        if self.pos and s != 206:
            raise BotError(
                "سرور از ادامه‌ی دانلود (Range) پشتیبانی نمی‌کنه، "
                "برای همین نمی‌شه بعد از قطعی از همون نقطه ادامه داد."
            )
        if "text/html" in resp.headers.get("Content-Type", "").lower():
            raise BotError(
                "این لینک یک صفحه‌ی وب هست نه خودِ فایل. "
                "باید «لینک دانلود مستقیم» رو بفرستی."
            )

    def _learn(self, resp: aiohttp.ClientResponse) -> None:
        if resp.status == 206:
            m = re.search(r"/(\d+)\s*$", resp.headers.get("Content-Range", ""))
            self.total = int(m.group(1)) if m else None
        else:
            cl = resp.headers.get("Content-Length", "")
            self.total = int(cl) if cl.isdigit() else None
        name = None
        cd = resp.content_disposition
        if cd is not None and cd.filename:
            name = cd.filename
        if not name:
            name = unquote(Path(urlparse(self.url).path).name)
        self.filename = safe_name(name)

    async def read_part(self, path: Path, size: int, on_progress) -> int:
        """Download up to `size` bytes (fewer at EOF) into `path`; returns bytes written.

        On a network error it reconnects with `Range: bytes=<pos>-` and continues
        exactly where it stopped, so nothing already written is lost.
        """
        written = 0
        attempt = 0
        with open(path, "wb") as f:
            while written < size:
                try:
                    if self.resp is None:
                        await self._open()
                    chunk = await self.resp.content.read(min(1 << 20, size - written))
                    if not chunk:  # EOF
                        if self.total is not None and self.pos < self.total:
                            raise Transient("connection closed early")
                        break
                    f.write(chunk)
                    written += len(chunk)
                    self.pos += len(chunk)
                    attempt = 0
                    await on_progress(written)
                except RETRYABLE as e:
                    attempt += 1
                    self.close()
                    if attempt > MAX_RETRIES:
                        raise BotError(
                            f"دانلود بعد از {MAX_RETRIES} بار تلاش ناموفق بود ({short_err(e)})."
                        ) from e
                    delay = min(60, 2**attempt)
                    log.warning("download error (%s); retry %d/%d", e, attempt, MAX_RETRIES)
                    await self.notify(
                        f"⚠️ دانلود قطع شد ({short_err(e)})\n"
                        f"🔁 تلاش مجدد {attempt}/{MAX_RETRIES} تا {delay} ثانیه‌ی دیگه — "
                        f"از بایت {fmt_size(self.pos)} ادامه می‌دم."
                    )
                    await asyncio.sleep(delay)
        return written


# --------------------------------------------------------------------------- #
# GitHub side
# --------------------------------------------------------------------------- #
class GitHub:
    def __init__(self, session: aiohttp.ClientSession, notify):
        self.s, self.notify = session, notify
        self.repo = f"{GITHUB_API}/repos/{GITHUB_OWNER}/{GITHUB_REPO}"
        self.h = {
            "Authorization": f"Bearer {GITHUB_TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        }

    @staticmethod
    def _raise_for(status: int, text: str) -> None:
        if status == 401:
            raise BotError("توکن GitHub نامعتبره (401). GITHUB_TOKEN رو چک کن.")
        if status == 404:
            raise BotError(
                "ریپوی GitHub پیدا نشد (404). GITHUB_OWNER / GITHUB_REPO و "
                "دسترسی توکن (اسکوپ repo) رو چک کن."
            )
        if status == 429 or status >= 500:
            raise Transient(f"GitHub HTTP {status}")
        if status == 403:
            raise BotError(f"GitHub دسترسی رو رد کرد (403): {text[:200]}")
        raise BotError(f"خطای GitHub (HTTP {status}): {text[:200]}")

    async def create_release(self, tag: str, title: str, body: str) -> dict:
        async def attempt() -> dict:
            async with self.s.post(
                f"{self.repo}/releases",
                json={"tag_name": tag, "name": title, "body": body,
                      "draft": False, "prerelease": False},
                headers=self.h,
            ) as r:
                if r.status == 201:
                    return await r.json()
                text = await r.text()
                if r.status == 422:
                    raise BotError(
                        "ساخت Release ناموفق بود (422). اگه ریپو کاملاً خالیه، "
                        f"یک فایل README توش بذار و دوباره امتحان کن. {text[:150]}"
                    )
                self._raise_for(r.status, text)

        return await with_retry(attempt, "ساخت Release در GitHub", self.notify)

    async def _delete_asset_if_exists(self, release_id: int, name: str) -> None:
        """A failed upload can leave a half-finished asset behind; remove it first."""
        async with self.s.get(
            f"{self.repo}/releases/{release_id}/assets",
            params={"per_page": 100}, headers=self.h,
        ) as r:
            if r.status != 200:
                return
            assets = await r.json()
        for a in assets:
            if a.get("name") == name:
                async with self.s.delete(
                    f"{self.repo}/releases/assets/{a['id']}", headers=self.h
                ):
                    pass

    async def upload_asset(self, release: dict, path: Path, name: str, label: str) -> dict:
        upload_url = release["upload_url"].split("{")[0]
        first = True

        async def attempt() -> dict:
            nonlocal first
            if not first:
                await self._delete_asset_if_exists(release["id"], name)
            first = False
            with open(path, "rb") as f:
                async with self.s.post(
                    upload_url,
                    params={"name": name},
                    data=f,  # aiohttp streams the file and sets Content-Length
                    headers={**self.h, "Content-Type": "application/octet-stream"},
                ) as r:
                    if r.status == 201:
                        return await r.json()
                    text = await r.text()
                    if r.status == 422 and "already_exists" in text:
                        raise Transient("asset already exists (partial upload)")
                    self._raise_for(r.status, text)

        return await with_retry(attempt, f"آپلود {label}", self.notify)


# --------------------------------------------------------------------------- #
# The job
# --------------------------------------------------------------------------- #
async def run_job(bot: Bot, chat_id: int, url: str, custom_title: str | None) -> None:
    status = Status(bot, chat_id)

    async def notify(text: str) -> None:
        await status.set(text, force=True)

    job_dir = WORK_DIR / f"{chat_id}-{int(time.time())}"
    job_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    uploaded: list[dict] = []
    release_url = ""

    try:
        timeout = aiohttp.ClientTimeout(total=None, sock_connect=30, sock_read=600)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            src = Source(session, url, notify)
            gh = GitHub(session, notify)

            await status.set("🔗 در حال اتصال به لینک دانلود...", force=True)
            await src.connect()

            filename = src.filename or "download.bin"
            total = src.total
            n_parts = math.ceil(total / CHUNK_SIZE) if total else None
            single = total is not None and total <= CHUNK_SIZE
            of_txt = f" از {n_parts}" if n_parts else ""

            stem = re.sub(r"[^A-Za-z0-9_-]+", "-", Path(filename).stem).strip("-")[:40] or "file"
            tag = f"{stem}-{datetime.now(timezone.utc):%Y%m%d-%H%M%S}"
            body = (
                f"Uploaded by nexus-bot.\n\nFile: `{filename}`\n\n"
                + ("" if single else
                   "The file is split into parts. Download all of them, then join:\n\n"
                   f"- Linux/macOS: `cat {filename}.part_* > {filename}`\n"
                   f"- Windows (cmd): `copy /b {filename}.part_* {filename}`\n")
            )
            await status.set("🏷 در حال ساخت Release در GitHub...", force=True)
            release = await gh.create_release(tag, custom_title or filename, body)
            release_url = release["html_url"]

            size_txt = fmt_size(total) if total else "نامشخص"
            await send(
                bot, chat_id,
                f"📄 <code>{html.escape(filename)}</code>\n"
                f"📏 حجم: {size_txt}"
                + (f" → {n_parts} پارت (هر پارت حداکثر {fmt_size(CHUNK_SIZE)})" if n_parts and n_parts > 1 else "")
                + "\n🚀 شروع شد. بعد از آپلود هر پارت بهت پیام می‌دم.",
            )

            index = 0
            while not (total is not None and src.pos >= total):
                part_no = index + 1
                name = filename if single else f"{filename}.part_{part_suffix(index)}"
                path = job_dir / name
                part_start = src.pos
                part_target = min(CHUNK_SIZE, total - part_start) if total else CHUNK_SIZE
                t0 = time.monotonic()

                async def on_progress(part_bytes: int) -> None:
                    if not status.due():
                        return
                    speed = part_bytes / max(time.monotonic() - t0, 1e-6)
                    overall = f" • کل: {src.pos / total * 100:.1f}%" if total else ""
                    await status.set(
                        f"⬇️ پارت {part_no}{of_txt}: {fmt_size(part_bytes)} / {fmt_size(part_target)}"
                        f"{overall}\n🚄 سرعت: {fmt_size(speed)}/s"
                    )

                written = await src.read_part(path, CHUNK_SIZE, on_progress)
                if written == 0:
                    path.unlink(missing_ok=True)
                    break

                await status.set(
                    f"⬆️ پارت {part_no}{of_txt}: در حال آپلود به GitHub ({fmt_size(written)})...",
                    force=True,
                )
                asset = await gh.upload_asset(release, path, name, f"پارت {part_no}")
                path.unlink(missing_ok=True)  # free the disk immediately
                uploaded.append(asset)

                done = f"{src.pos / total * 100:.1f}%" if total else fmt_size(src.pos)
                await send(
                    bot, chat_id,
                    f"✅ <b>پارت {part_no}{of_txt}</b> آپلود شد\n"
                    f"📦 <code>{html.escape(name)}</code> ({fmt_size(written)})\n"
                    f"📊 پیشرفت کل: {done}\n"
                    f"🔗 <a href=\"{html.escape(asset['browser_download_url'], quote=True)}\">لینک دانلود این پارت</a>",
                )
                index += 1

            src.close()
            if not uploaded:
                raise BotError("فایل خالی بود و چیزی آپلود نشد.")

            join_help = ""
            if len(uploaded) > 1:
                fn = html.escape(filename)
                join_help = (
                    "\n\n🧩 <b>ترکیب پارت‌ها:</b>\n"
                    f"Linux/macOS: <code>cat {fn}.part_* &gt; {fn}</code>\n"
                    f"Windows: <code>copy /b {fn}.part_* {fn}</code>"
                )
            await status.set("✅ تمام شد.", force=True)
            await send(
                bot, chat_id,
                f"🎉 <b>تموم شد!</b> {len(uploaded)} پارت • "
                f"{fmt_size(src.pos)} • {fmt_duration(time.monotonic() - started)}\n"
                f"🔗 <a href=\"{html.escape(release_url, quote=True)}\">صفحه‌ی Release در GitHub</a>"
                f"{join_help}",
            )

    except asyncio.CancelledError:
        await send(bot, chat_id, _partial_note("⛔ عملیات لغو شد.", uploaded, release_url))
        raise
    except BotError as e:
        await send(bot, chat_id, _partial_note(f"❌ {html.escape(str(e))}", uploaded, release_url))
    except OSError as e:
        if e.errno == errno.ENOSPC:
            msg = ("❌ فضای دیسک سرور تموم شد (No space left on device). "
                   "مقدار CHUNK_SIZE_MB رو تو Variables کمتر کن (مثلاً 500) و دوباره امتحان کن.")
        else:
            msg = f"❌ خطای سیستمی: {html.escape(short_err(e))}"
        await send(bot, chat_id, _partial_note(msg, uploaded, release_url))
    except Exception as e:  # noqa: BLE001
        log.exception("job crashed")
        await send(bot, chat_id, _partial_note(
            f"❌ خطای غیرمنتظره: {html.escape(short_err(e))}", uploaded, release_url))
    finally:
        shutil.rmtree(job_dir, ignore_errors=True)


def _partial_note(msg: str, uploaded: list[dict], release_url: str) -> str:
    if uploaded and release_url:
        return (f"{msg}\n\n📦 {len(uploaded)} پارت تا اینجا آپلود شده بود: "
                f"<a href=\"{html.escape(release_url, quote=True)}\">Release</a>")
    return msg


# --------------------------------------------------------------------------- #
# Telegram handlers
# --------------------------------------------------------------------------- #
dp = Dispatcher()
CURRENT: asyncio.Task | None = None  # only one job at a time (shared disk)

HELP_TEXT = (
    "سلام! 👋 من فایل‌های بزرگ رو از <b>لینک دانلود مستقیم</b> می‌گیرم، تکه‌تکه می‌کنم و "
    "روی GitHub Release آپلود می‌کنم.\n\n"
    "<b>طرز استفاده:</b>\n"
    "1️⃣ توی سایت Nexus روی <b>Manual → Slow download</b> بزن و صبر کن دانلود توی مرورگر شروع بشه.\n"
    "2️⃣ لینک دانلود رو کپی کن: توی Chrome برو به <code>chrome://downloads</code> (Ctrl+J) → روی "
    "آدرس زیر اسم فایل راست‌کلیک → Copy link address. (Firefox: توی پنل Downloads راست‌کلیک → "
    "Copy Download Link.) بعدش دانلود مرورگر رو Cancel کن.\n"
    "3️⃣ همون لینک رو <b>سریع</b> اینجا بفرست (لینک‌ها زود منقضی می‌شن).\n\n"
    "می‌تونی بعد از لینک، یک اسم دلخواه برای Release هم بنویسی.\n\n"
    "/cancel — لغو کار در حال اجرا\n"
    "/id — نمایش آیدی عددی تو"
)


def is_allowed(user_id: int | None) -> bool:
    return not ALLOWED_USERS or (user_id in ALLOWED_USERS)


@dp.message(CommandStart())
@dp.message(Command("help"))
async def cmd_start(message: Message) -> None:
    if not is_allowed(message.from_user.id if message.from_user else None):
        await message.answer("⛔ دسترسی نداری.")
        return
    await message.answer(HELP_TEXT)


@dp.message(Command("id"))
async def cmd_id(message: Message) -> None:
    uid = message.from_user.id if message.from_user else "?"
    await message.answer(f"آیدی عددی تو: <code>{uid}</code>")


@dp.message(Command("cancel"))
async def cmd_cancel(message: Message) -> None:
    if not is_allowed(message.from_user.id if message.from_user else None):
        return
    if CURRENT is not None and not CURRENT.done():
        CURRENT.cancel()
    else:
        await message.answer("الان کاری در حال اجرا نیست.")


@dp.message(F.text)
async def on_text(message: Message, bot: Bot) -> None:
    global CURRENT
    if not is_allowed(message.from_user.id if message.from_user else None):
        await message.answer("⛔ دسترسی نداری.")
        return

    m = URL_RE.search(message.text or "")
    if not m:
        await message.answer("لینک دانلود مستقیم رو بفرست. راهنما: /help")
        return
    url = m.group(0).rstrip(".,;)]>")
    extra = ((message.text or "").replace(m.group(0), "", 1)).strip() or None

    if looks_like_mod_page(url):
        await message.answer(
            "این لینک <b>صفحه‌ی مود</b> هست؛ من لینک <b>دانلود مستقیم</b> می‌خوام.\n\n"
            "توی صفحه‌ی مود، تب Files → Manual → Slow download رو بزن، وقتی دانلود شروع شد "
            "لینکش رو از مرورگر کپی کن و اینجا بفرست. راهنمای کامل: /help"
        )
        return

    if CURRENT is not None and not CURRENT.done():
        await message.answer("⏳ یک کار در حال اجراست. صبر کن تموم بشه یا /cancel بزن.")
        return

    CURRENT = asyncio.create_task(run_job(bot, message.chat.id, url, extra))


# --------------------------------------------------------------------------- #
async def main() -> None:
    missing = [k for k, v in {
        "BOT_TOKEN": BOT_TOKEN, "GITHUB_TOKEN": GITHUB_TOKEN,
        "GITHUB_OWNER": GITHUB_OWNER, "GITHUB_REPO": GITHUB_REPO,
    }.items() if not v]
    if missing:
        raise SystemExit(f"Missing environment variables: {', '.join(missing)}")
    if not ALLOWED_USERS:
        log.warning("ALLOWED_USER_IDS is empty: ANYONE who finds the bot can use it!")

    WORK_DIR.mkdir(parents=True, exist_ok=True)
    bot = Bot(
        BOT_TOKEN,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML, link_preview_is_disabled=True),
    )
    await bot.delete_webhook(drop_pending_updates=True)
    log.info("Bot started. chunk=%s retries=%d", fmt_size(CHUNK_SIZE), MAX_RETRIES)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
