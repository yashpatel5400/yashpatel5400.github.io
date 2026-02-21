#!/usr/bin/env python3
"""Authenticated draft API backed by SQLite.

Supports two auth modes:
1) Static bearer token via DRAFT_DB_TOKEN (legacy/simple).
2) Session token flow via POST /api/session using owner passphrase + HMAC-signed short-lived tokens.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import json
import os
import sqlite3
import threading
import time
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse

MAX_JSON_BODY_BYTES = 2 * 1024 * 1024


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def b64url_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def b64url_decode(text: str) -> bytes:
    padding = "=" * ((4 - len(text) % 4) % 4)
    return base64.urlsafe_b64decode((text + padding).encode("ascii"))


class DraftStore:
    def __init__(self, db_path: Path) -> None:
        self._conn = sqlite3.connect(str(db_path), check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._lock = threading.Lock()
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA synchronous=NORMAL")
        self._conn.execute(
            """
            CREATE TABLE IF NOT EXISTS drafts (
              draft_id TEXT PRIMARY KEY,
              title TEXT NOT NULL DEFAULT '',
              draft_date TEXT NOT NULL DEFAULT '',
              body TEXT NOT NULL DEFAULT '',
              filename TEXT NOT NULL DEFAULT '',
              markdown TEXT NOT NULL DEFAULT '',
              updated_at TEXT NOT NULL
            )
            """
        )
        self._conn.commit()

    def get(self, draft_id: str) -> dict | None:
        with self._lock:
            row = self._conn.execute(
                """
                SELECT draft_id, title, draft_date, body, filename, markdown, updated_at
                FROM drafts
                WHERE draft_id = ?
                """,
                (draft_id,),
            ).fetchone()
        if row is None:
            return None
        return dict(row)

    def upsert(self, draft_id: str, payload: dict) -> dict:
        title = str(payload.get("title", ""))
        draft_date = str(payload.get("date", ""))
        body = str(payload.get("body", ""))
        filename = str(payload.get("filename", ""))
        markdown = str(payload.get("markdown", ""))
        updated_at = now_utc_iso()

        with self._lock:
            self._conn.execute(
                """
                INSERT INTO drafts (draft_id, title, draft_date, body, filename, markdown, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(draft_id) DO UPDATE SET
                  title = excluded.title,
                  draft_date = excluded.draft_date,
                  body = excluded.body,
                  filename = excluded.filename,
                  markdown = excluded.markdown,
                  updated_at = excluded.updated_at
                """,
                (draft_id, title, draft_date, body, filename, markdown, updated_at),
            )
            self._conn.commit()
        return {
            "draft_id": draft_id,
            "title": title,
            "draft_date": draft_date,
            "body": body,
            "filename": filename,
            "markdown": markdown,
            "updated_at": updated_at,
        }


class AuthManager:
    def __init__(
        self,
        static_token: str,
        owner_passphrase: str,
        session_secret: str,
        session_ttl_seconds: int,
        login_window_seconds: int,
        login_max_attempts: int,
    ) -> None:
        self._static_token = static_token.strip()
        self._owner_passphrase = owner_passphrase
        self._session_secret = session_secret.encode("utf-8") if session_secret else b""
        self.session_ttl_seconds = max(300, int(session_ttl_seconds))
        self._login_window_seconds = max(30, int(login_window_seconds))
        self._login_max_attempts = max(3, int(login_max_attempts))
        self._failed_attempts: dict[str, list[float]] = {}
        self._lock = threading.Lock()

    @property
    def has_static_token(self) -> bool:
        return bool(self._static_token)

    @property
    def supports_session(self) -> bool:
        return bool(self._owner_passphrase) and bool(self._session_secret)

    @property
    def has_any_auth(self) -> bool:
        return self.has_static_token or self.supports_session

    def _prune_locked(self, client_id: str, now_ts: float) -> list[float]:
        attempts = self._failed_attempts.get(client_id, [])
        attempts = [ts for ts in attempts if (now_ts - ts) < self._login_window_seconds]
        if attempts:
            self._failed_attempts[client_id] = attempts
        else:
            self._failed_attempts.pop(client_id, None)
        return attempts

    def is_rate_limited(self, client_id: str) -> bool:
        now_ts = time.time()
        with self._lock:
            attempts = self._prune_locked(client_id, now_ts)
            return len(attempts) >= self._login_max_attempts

    def record_failed_attempt(self, client_id: str) -> None:
        now_ts = time.time()
        with self._lock:
            attempts = self._prune_locked(client_id, now_ts)
            attempts.append(now_ts)
            self._failed_attempts[client_id] = attempts

    def record_success(self, client_id: str) -> None:
        with self._lock:
            self._failed_attempts.pop(client_id, None)

    def verify_owner_passphrase(self, passphrase: str) -> bool:
        if not self.supports_session:
            return False
        return hmac.compare_digest(passphrase, self._owner_passphrase)

    def issue_session_token(self) -> str:
        if not self.supports_session:
            raise RuntimeError("Session auth not configured")
        issued_at = int(time.time())
        payload = {
            "sub": "owner",
            "iat": issued_at,
            "exp": issued_at + self.session_ttl_seconds,
        }
        payload_b64 = b64url_encode(json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8"))
        signature = hmac.new(self._session_secret, payload_b64.encode("utf-8"), hashlib.sha256).digest()
        return payload_b64 + "." + b64url_encode(signature)

    def _verify_session_token(self, token: str) -> bool:
        if not self.supports_session:
            return False
        parts = token.split(".")
        if len(parts) != 2:
            return False
        payload_b64, signature_b64 = parts
        try:
            provided_sig = b64url_decode(signature_b64)
            expected_sig = hmac.new(
                self._session_secret, payload_b64.encode("utf-8"), hashlib.sha256
            ).digest()
            if not hmac.compare_digest(provided_sig, expected_sig):
                return False

            payload_raw = b64url_decode(payload_b64)
            payload = json.loads(payload_raw.decode("utf-8"))
            if not isinstance(payload, dict):
                return False
            if payload.get("sub") != "owner":
                return False
            expires_at = int(payload.get("exp", 0))
            return int(time.time()) <= expires_at
        except Exception:  # noqa: BLE001
            return False

    def authorized(self, auth_header: str) -> bool:
        if not auth_header.startswith("Bearer "):
            return False
        token = auth_header[len("Bearer ") :].strip()
        if not token:
            return False
        if self.has_static_token and hmac.compare_digest(token, self._static_token):
            return True
        return self._verify_session_token(token)


class DraftApiServer(ThreadingHTTPServer):
    def __init__(
        self,
        server_address: tuple[str, int],
        handler_class: type[BaseHTTPRequestHandler],
        store: DraftStore,
        auth_manager: AuthManager,
        allowed_origins: set[str],
    ) -> None:
        super().__init__(server_address, handler_class)
        self.store = store
        self.auth_manager = auth_manager
        self.allowed_origins = allowed_origins


class DraftApiHandler(BaseHTTPRequestHandler):
    server_version = "DraftApi/2.0"

    def log_message(self, fmt: str, *args) -> None:
        super().log_message(fmt, *args)

    def _send_json(self, status: int, payload: dict, origin: str | None = None) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self._set_cors_headers(origin)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _set_cors_headers(self, origin: str | None) -> None:
        resolved = self._resolve_allowed_origin(origin)
        if resolved is not None:
            self.send_header("Access-Control-Allow-Origin", resolved)
            self.send_header("Vary", "Origin")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Authorization")
        self.send_header("Access-Control-Allow-Methods", "GET, PUT, POST, OPTIONS")

    def _resolve_allowed_origin(self, origin: str | None) -> str | None:
        allowed = self.server.allowed_origins
        if "*" in allowed:
            return "*" if origin is None else origin
        if origin and origin in allowed:
            return origin
        return None

    def _read_json(self) -> dict:
        raw_length = self.headers.get("Content-Length")
        if raw_length is None:
            raise ValueError("Missing Content-Length")
        length = int(raw_length)
        if length < 0 or length > MAX_JSON_BODY_BYTES:
            raise ValueError("Request too large")
        body = self.rfile.read(length)
        payload = json.loads(body.decode("utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("Body must be a JSON object")
        return payload

    def _authorized(self) -> bool:
        return self.server.auth_manager.authorized(self.headers.get("Authorization", ""))

    def _client_id(self) -> str:
        forwarded = self.headers.get("CF-Connecting-IP") or self.headers.get("X-Forwarded-For")
        if forwarded:
            return forwarded.split(",")[0].strip()
        if self.client_address and self.client_address[0]:
            return self.client_address[0]
        return "unknown"

    def _draft_id_from_path(self) -> str | None:
        parsed = urlparse(self.path)
        prefix = "/api/drafts/"
        if not parsed.path.startswith(prefix):
            return None
        draft_id = unquote(parsed.path[len(prefix) :].strip())
        if not draft_id or "/" in draft_id:
            return None
        return draft_id

    def do_OPTIONS(self) -> None:
        origin = self.headers.get("Origin")
        self.send_response(204)
        self._set_cors_headers(origin)
        self.end_headers()

    def do_GET(self) -> None:
        origin = self.headers.get("Origin")
        parsed = urlparse(self.path)

        if parsed.path == "/health":
            self._send_json(
                200,
                {
                    "ok": True,
                    "time": now_utc_iso(),
                    "session_auth": self.server.auth_manager.supports_session,
                },
                origin,
            )
            return

        draft_id = self._draft_id_from_path()
        if draft_id is None:
            self._send_json(404, {"error": "Not found"}, origin)
            return

        if not self._authorized():
            self._send_json(401, {"error": "Unauthorized"}, origin)
            return

        draft = self.server.store.get(draft_id)
        if draft is None:
            self._send_json(404, {"error": "Draft not found"}, origin)
            return

        self._send_json(200, {"draft": draft}, origin)

    def do_POST(self) -> None:
        origin = self.headers.get("Origin")
        parsed = urlparse(self.path)

        if parsed.path != "/api/session":
            self._send_json(404, {"error": "Not found"}, origin)
            return

        if not self.server.auth_manager.supports_session:
            self._send_json(404, {"error": "Not found"}, origin)
            return

        client_id = self._client_id()
        if self.server.auth_manager.is_rate_limited(client_id):
            self._send_json(429, {"error": "Too many attempts. Try again later."}, origin)
            return

        try:
            payload = self._read_json()
        except Exception as exc:  # noqa: BLE001
            self._send_json(400, {"error": f"Invalid JSON payload: {exc}"}, origin)
            return

        passphrase = payload.get("passphrase")
        if not isinstance(passphrase, str) or not self.server.auth_manager.verify_owner_passphrase(passphrase):
            self.server.auth_manager.record_failed_attempt(client_id)
            self._send_json(401, {"error": "Unauthorized"}, origin)
            return

        self.server.auth_manager.record_success(client_id)
        token = self.server.auth_manager.issue_session_token()
        self._send_json(
            200,
            {"token": token, "expires_in": self.server.auth_manager.session_ttl_seconds},
            origin,
        )

    def do_PUT(self) -> None:
        origin = self.headers.get("Origin")
        draft_id = self._draft_id_from_path()
        if draft_id is None:
            self._send_json(404, {"error": "Not found"}, origin)
            return

        if not self._authorized():
            self._send_json(401, {"error": "Unauthorized"}, origin)
            return

        try:
            payload = self._read_json()
        except Exception as exc:  # noqa: BLE001
            self._send_json(400, {"error": f"Invalid JSON payload: {exc}"}, origin)
            return

        draft = self.server.store.upsert(draft_id, payload)
        self._send_json(200, {"draft": draft}, origin)


def parse_allowed_origins(value: str) -> set[str]:
    origins = {item.strip() for item in value.split(",") if item.strip()}
    if not origins:
        return {"*"}
    return origins


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the SQLite-backed draft API server.")
    parser.add_argument("--host", default=os.getenv("DRAFT_DB_HOST", "127.0.0.1"))
    parser.add_argument(
        "--port",
        type=int,
        default=int(os.getenv("DRAFT_DB_PORT", os.getenv("PORT", "8787"))),
    )
    parser.add_argument(
        "--db",
        default=os.getenv("DRAFT_DB_PATH", "draft_api/drafts.sqlite3"),
        help="Path to SQLite database file.",
    )
    parser.add_argument(
        "--origins",
        default=os.getenv(
            "DRAFT_DB_ALLOWED_ORIGINS",
            "http://127.0.0.1:4000,http://localhost:4000,https://yashpatel5400.github.io,https://ypatel.io",
        ),
        help="Comma-separated list of allowed CORS origins. Use '*' only if needed.",
    )
    args = parser.parse_args()

    static_token = os.getenv("DRAFT_DB_TOKEN", "").strip()
    owner_passphrase = os.getenv("DRAFT_DB_OWNER_PASSPHRASE", "")
    session_secret = os.getenv("DRAFT_DB_SESSION_SECRET", "")
    session_ttl_seconds = int(os.getenv("DRAFT_DB_SESSION_TTL_SECONDS", "28800"))
    login_window_seconds = int(os.getenv("DRAFT_DB_LOGIN_WINDOW_SECONDS", "300"))
    login_max_attempts = int(os.getenv("DRAFT_DB_LOGIN_MAX_ATTEMPTS", "10"))

    if bool(owner_passphrase) ^ bool(session_secret):
        raise SystemExit(
            "Set both DRAFT_DB_OWNER_PASSPHRASE and DRAFT_DB_SESSION_SECRET, or set neither."
        )

    auth_manager = AuthManager(
        static_token=static_token,
        owner_passphrase=owner_passphrase,
        session_secret=session_secret,
        session_ttl_seconds=session_ttl_seconds,
        login_window_seconds=login_window_seconds,
        login_max_attempts=login_max_attempts,
    )
    if not auth_manager.has_any_auth:
        raise SystemExit(
            "Set DRAFT_DB_TOKEN or set DRAFT_DB_OWNER_PASSPHRASE with DRAFT_DB_SESSION_SECRET."
        )

    db_path = Path(args.db).expanduser().resolve()
    db_path.parent.mkdir(parents=True, exist_ok=True)
    store = DraftStore(db_path)
    allowed_origins = parse_allowed_origins(args.origins)

    server = DraftApiServer((args.host, args.port), DraftApiHandler, store, auth_manager, allowed_origins)
    print(
        f"Draft API listening on http://{args.host}:{args.port} "
        f"(db={db_path}, origins={sorted(allowed_origins)}, session_auth={auth_manager.supports_session})"
    )
    server.serve_forever()


if __name__ == "__main__":
    main()
