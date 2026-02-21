#!/usr/bin/env python3
"""Authenticated draft API backed by SQLite and GitHub publishing."""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import json
import os
import re
import sqlite3
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

MAX_JSON_BODY_BYTES = 2 * 1024 * 1024
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
SAFE_FILENAME_RE = re.compile(r"^[A-Za-z0-9._-]+\.md$")


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def today_utc_date() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def b64url_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def b64url_decode(text: str) -> bytes:
    padding = "=" * ((4 - len(text) % 4) % 4)
    return base64.urlsafe_b64decode((text + padding).encode("ascii"))


def yaml_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"')


def slugify(text: str) -> str:
    normalized = (text or "").lower().strip()
    normalized = re.sub(r"['\"]", "", normalized)
    normalized = re.sub(r"[^a-z0-9]+", "-", normalized)
    normalized = normalized.strip("-")
    return normalized or "new-post"


def split_front_matter(markdown: str) -> tuple[dict[str, str], str]:
    text = markdown or ""
    if not text.startswith("---"):
        return {}, text

    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return {}, text

    front_matter: dict[str, str] = {}
    idx = 1
    while idx < len(lines):
        line = lines[idx]
        if line.strip() == "---":
            idx += 1
            break
        if ":" in line:
            key, value = line.split(":", 1)
            cleaned = value.strip().strip('"').strip("'")
            front_matter[key.strip()] = cleaned
        idx += 1

    body = "\n".join(lines[idx:]).lstrip("\n")
    return front_matter, body


def build_markdown(title: str, post_date: str, body: str) -> str:
    content = (body or "").rstrip("\n")
    front_matter = [
        "---",
        "layout: post",
        f'title: "{yaml_escape(title)}"',
        f"date: {post_date}",
        "---",
        "",
    ]
    return "\n".join(front_matter) + content + "\n"


def guess_post_title_from_filename(filename: str) -> str:
    stem = filename[:-3] if filename.endswith(".md") else filename
    stem = re.sub(r"^\d{4}-\d{2}-\d{2}-", "", stem)
    words = [word for word in stem.split("-") if word]
    if not words:
        return "Untitled"
    return " ".join(word.capitalize() for word in words)


class DraftStore:
    def __init__(self, db_path: Path) -> None:
        self._conn = sqlite3.connect(str(db_path), check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._lock = threading.Lock()
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA synchronous=NORMAL")
        self._ensure_schema()

    def _ensure_schema(self) -> None:
        with self._lock:
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS drafts (
                  draft_id TEXT PRIMARY KEY,
                  title TEXT NOT NULL DEFAULT '',
                  draft_date TEXT NOT NULL DEFAULT '',
                  body TEXT NOT NULL DEFAULT '',
                  filename TEXT NOT NULL DEFAULT '',
                  markdown TEXT NOT NULL DEFAULT '',
                  source_post_filename TEXT NOT NULL DEFAULT '',
                  updated_at TEXT NOT NULL
                )
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS published_posts (
                  filename TEXT PRIMARY KEY,
                  title TEXT NOT NULL DEFAULT '',
                  post_date TEXT NOT NULL DEFAULT '',
                  body TEXT NOT NULL DEFAULT '',
                  markdown TEXT NOT NULL DEFAULT '',
                  html_url TEXT NOT NULL DEFAULT '',
                  sha TEXT NOT NULL DEFAULT '',
                  updated_at TEXT NOT NULL
                )
                """
            )

            columns = {
                row["name"]
                for row in self._conn.execute("PRAGMA table_info(drafts)").fetchall()
            }
            if "source_post_filename" not in columns:
                self._conn.execute(
                    "ALTER TABLE drafts ADD COLUMN source_post_filename TEXT NOT NULL DEFAULT ''"
                )

            self._conn.commit()

    def list_drafts(self, limit: int = 200) -> list[dict[str, Any]]:
        with self._lock:
            rows = self._conn.execute(
                """
                SELECT draft_id, title, draft_date, filename, source_post_filename, updated_at
                FROM drafts
                ORDER BY updated_at DESC
                LIMIT ?
                """,
                (max(1, int(limit)),),
            ).fetchall()
        return [dict(row) for row in rows]

    def get_draft(self, draft_id: str) -> dict[str, Any] | None:
        with self._lock:
            row = self._conn.execute(
                """
                SELECT draft_id, title, draft_date, body, filename, markdown, source_post_filename, updated_at
                FROM drafts
                WHERE draft_id = ?
                """,
                (draft_id,),
            ).fetchone()
        if row is None:
            return None
        return dict(row)

    def upsert_draft(self, draft_id: str, payload: dict[str, Any]) -> dict[str, Any]:
        title = str(payload.get("title", "")).strip()
        draft_date = str(payload.get("date", "")).strip()
        body = str(payload.get("body", ""))
        filename = str(payload.get("filename", "")).strip()
        markdown = str(payload.get("markdown", ""))
        source_post_filename = str(payload.get("source_post_filename", "")).strip()
        updated_at = now_utc_iso()

        if not draft_date:
            draft_date = today_utc_date()
        if not filename and title:
            filename = f"{draft_date}-{slugify(title)}.md"
        if not markdown and title:
            markdown = build_markdown(title, draft_date, body)

        with self._lock:
            self._conn.execute(
                """
                INSERT INTO drafts (
                  draft_id, title, draft_date, body, filename, markdown, source_post_filename, updated_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(draft_id) DO UPDATE SET
                  title = excluded.title,
                  draft_date = excluded.draft_date,
                  body = excluded.body,
                  filename = excluded.filename,
                  markdown = excluded.markdown,
                  source_post_filename = excluded.source_post_filename,
                  updated_at = excluded.updated_at
                """,
                (
                    draft_id,
                    title,
                    draft_date,
                    body,
                    filename,
                    markdown,
                    source_post_filename,
                    updated_at,
                ),
            )
            self._conn.commit()

        return {
            "draft_id": draft_id,
            "title": title,
            "draft_date": draft_date,
            "body": body,
            "filename": filename,
            "markdown": markdown,
            "source_post_filename": source_post_filename,
            "updated_at": updated_at,
        }

    def upsert_published_post(self, payload: dict[str, Any]) -> dict[str, Any]:
        filename = str(payload.get("filename", "")).strip()
        title = str(payload.get("title", "")).strip()
        post_date = str(payload.get("date", "")).strip()
        body = str(payload.get("body", ""))
        markdown = str(payload.get("markdown", ""))
        html_url = str(payload.get("html_url", "")).strip()
        sha = str(payload.get("sha", "")).strip()
        updated_at = now_utc_iso()

        with self._lock:
            self._conn.execute(
                """
                INSERT INTO published_posts (
                  filename, title, post_date, body, markdown, html_url, sha, updated_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(filename) DO UPDATE SET
                  title = excluded.title,
                  post_date = excluded.post_date,
                  body = excluded.body,
                  markdown = excluded.markdown,
                  html_url = excluded.html_url,
                  sha = excluded.sha,
                  updated_at = excluded.updated_at
                """,
                (filename, title, post_date, body, markdown, html_url, sha, updated_at),
            )
            self._conn.commit()

        return {
            "filename": filename,
            "title": title,
            "date": post_date,
            "body": body,
            "markdown": markdown,
            "html_url": html_url,
            "sha": sha,
            "updated_at": updated_at,
        }

    def list_cached_published_posts(self, limit: int = 300) -> list[dict[str, Any]]:
        with self._lock:
            rows = self._conn.execute(
                """
                SELECT filename, title, post_date AS date, html_url, updated_at
                FROM published_posts
                ORDER BY post_date DESC, filename DESC
                LIMIT ?
                """,
                (max(1, int(limit)),),
            ).fetchall()
        return [dict(row) for row in rows]


class GitHubPublisher:
    def __init__(self, token: str, repo: str, branch: str, timeout_seconds: int) -> None:
        self.token = token.strip()
        self.repo = repo.strip()
        self.branch = (branch or "master").strip() or "master"
        self.timeout_seconds = max(5, int(timeout_seconds))

    @property
    def configured(self) -> bool:
        return bool(self.token and self.repo)

    def _json_request(
        self,
        method: str,
        api_path: str,
        query: dict[str, str] | None = None,
        payload: dict[str, Any] | None = None,
    ) -> tuple[int, Any]:
        url = "https://api.github.com" + api_path
        if query:
            url += "?" + urllib.parse.urlencode(query)

        headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {self.token}",
            "User-Agent": "ypatel-draft-api",
            "X-GitHub-Api-Version": "2022-11-28",
        }
        body = None
        if payload is not None:
            body = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"

        request = urllib.request.Request(url, data=body, headers=headers, method=method.upper())

        try:
            with urllib.request.urlopen(request, timeout=self.timeout_seconds) as response:
                raw = response.read().decode("utf-8", "replace")
                parsed = json.loads(raw) if raw else None
                return int(response.status), parsed
        except urllib.error.HTTPError as exc:
            raw = exc.read().decode("utf-8", "replace")
            parsed = None
            if raw:
                try:
                    parsed = json.loads(raw)
                except Exception:  # noqa: BLE001
                    parsed = {"message": raw}
            return int(exc.code), parsed

    @staticmethod
    def _github_error(status: int, payload: Any) -> str:
        if isinstance(payload, dict):
            message = str(payload.get("message", "")).strip()
            if message:
                return f"GitHub API {status}: {message}"
        return f"GitHub API {status} request failed."

    def _read_file(self, repo_path: str) -> dict[str, Any] | None:
        status, payload = self._json_request(
            "GET",
            f"/repos/{self.repo}/contents/{urllib.parse.quote(repo_path, safe='/')}",
            query={"ref": self.branch},
        )
        if status == 404:
            return None
        if status != 200 or not isinstance(payload, dict):
            raise RuntimeError(self._github_error(status, payload))
        return payload

    def list_posts(self) -> list[dict[str, Any]]:
        if not self.configured:
            raise RuntimeError("GitHub publishing is not configured.")

        status, payload = self._json_request(
            "GET",
            f"/repos/{self.repo}/contents/{urllib.parse.quote('_posts', safe='/')}",
            query={"ref": self.branch},
        )
        if status != 200 or not isinstance(payload, list):
            raise RuntimeError(self._github_error(status, payload))

        posts: list[dict[str, Any]] = []
        for item in payload:
            if not isinstance(item, dict):
                continue
            name = str(item.get("name", "")).strip()
            if not name.endswith(".md"):
                continue
            date_match = re.match(r"^(\d{4}-\d{2}-\d{2})-", name)
            guessed_date = date_match.group(1) if date_match else ""
            posts.append(
                {
                    "filename": name,
                    "title": guess_post_title_from_filename(name),
                    "date": guessed_date,
                    "html_url": str(item.get("html_url", "")).strip(),
                    "sha": str(item.get("sha", "")).strip(),
                }
            )

        posts.sort(key=lambda post: (post.get("date", ""), post.get("filename", "")), reverse=True)
        return posts

    def load_post(self, filename: str) -> dict[str, Any] | None:
        if not self.configured:
            raise RuntimeError("GitHub publishing is not configured.")

        repo_path = f"_posts/{filename}"
        payload = self._read_file(repo_path)
        if payload is None:
            return None

        encoded = str(payload.get("content", "")).replace("\n", "")
        if not encoded:
            raise RuntimeError("GitHub post payload missing content.")

        try:
            raw_bytes = base64.b64decode(encoded, validate=False)
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError(f"Unable to decode GitHub post content: {exc}") from exc

        markdown = raw_bytes.decode("utf-8", "replace")
        front_matter, body = split_front_matter(markdown)
        title = front_matter.get("title", "").strip() or guess_post_title_from_filename(filename)
        post_date = front_matter.get("date", "").strip()
        if len(post_date) >= 10:
            post_date = post_date[:10]
        if not DATE_RE.match(post_date):
            date_match = re.match(r"^(\d{4}-\d{2}-\d{2})-", filename)
            post_date = date_match.group(1) if date_match else ""

        return {
            "filename": filename,
            "title": title,
            "date": post_date,
            "body": body,
            "markdown": markdown,
            "sha": str(payload.get("sha", "")).strip(),
            "html_url": str(payload.get("html_url", "")).strip(),
        }

    def publish_post(
        self,
        *,
        title: str,
        post_date: str,
        body: str,
        requested_filename: str,
    ) -> dict[str, Any]:
        if not self.configured:
            raise RuntimeError("GitHub publishing is not configured.")

        clean_title = title.strip()
        clean_body = body.strip()
        clean_date = post_date.strip() or today_utc_date()

        if not clean_title:
            raise RuntimeError("Title is required.")
        if not clean_body:
            raise RuntimeError("Markdown body is required.")
        if not DATE_RE.match(clean_date):
            raise RuntimeError("Date must be in YYYY-MM-DD format.")

        filename = requested_filename.strip()
        if not filename:
            filename = f"{clean_date}-{slugify(clean_title)}.md"
        if not SAFE_FILENAME_RE.match(filename):
            raise RuntimeError("Invalid post filename.")

        markdown = build_markdown(clean_title, clean_date, clean_body)
        repo_path = f"_posts/{filename}"
        existing = self._read_file(repo_path)
        existing_sha = str(existing.get("sha", "")).strip() if existing else ""
        message_prefix = "Update post" if existing_sha else "Publish post"
        message = f"{message_prefix}: {filename}"

        payload: dict[str, Any] = {
            "message": message,
            "content": base64.b64encode(markdown.encode("utf-8")).decode("ascii"),
            "branch": self.branch,
        }
        if existing_sha:
            payload["sha"] = existing_sha

        status, response_payload = self._json_request(
            "PUT",
            f"/repos/{self.repo}/contents/{urllib.parse.quote(repo_path, safe='/')}",
            payload=payload,
        )
        if status not in (200, 201) or not isinstance(response_payload, dict):
            raise RuntimeError(self._github_error(status, response_payload))

        content = response_payload.get("content") if isinstance(response_payload.get("content"), dict) else {}
        resolved_sha = str(content.get("sha", "")).strip()
        html_url = str(content.get("html_url", "")).strip()

        return {
            "filename": filename,
            "title": clean_title,
            "date": clean_date,
            "body": clean_body,
            "markdown": markdown,
            "sha": resolved_sha,
            "html_url": html_url,
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
        publisher: GitHubPublisher,
    ) -> None:
        super().__init__(server_address, handler_class)
        self.store = store
        self.auth_manager = auth_manager
        self.allowed_origins = allowed_origins
        self.publisher = publisher


class DraftApiHandler(BaseHTTPRequestHandler):
    server_version = "DraftApi/3.0"

    def log_message(self, fmt: str, *args) -> None:
        super().log_message(fmt, *args)

    def _send_json(self, status: int, payload: dict[str, Any], origin: str | None = None) -> None:
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

    def _read_json(self) -> dict[str, Any]:
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
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/api/drafts/"
        if not parsed.path.startswith(prefix):
            return None
        draft_id = urllib.parse.unquote(parsed.path[len(prefix) :].strip())
        if not draft_id or "/" in draft_id:
            return None
        return draft_id

    def _post_filename_from_path(self) -> str | None:
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/api/posts/"
        if not parsed.path.startswith(prefix):
            return None
        filename = urllib.parse.unquote(parsed.path[len(prefix) :].strip())
        if not filename or "/" in filename or not SAFE_FILENAME_RE.match(filename):
            return None
        return filename

    def do_OPTIONS(self) -> None:
        origin = self.headers.get("Origin")
        self.send_response(204)
        self._set_cors_headers(origin)
        self.end_headers()

    def do_GET(self) -> None:
        origin = self.headers.get("Origin")
        parsed = urllib.parse.urlparse(self.path)

        if parsed.path == "/health":
            self._send_json(
                200,
                {
                    "ok": True,
                    "time": now_utc_iso(),
                    "session_auth": self.server.auth_manager.supports_session,
                    "github_publish_enabled": self.server.publisher.configured,
                    "github_repo": self.server.publisher.repo,
                    "github_branch": self.server.publisher.branch,
                },
                origin,
            )
            return

        if parsed.path == "/api/drafts":
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            drafts = self.server.store.list_drafts()
            self._send_json(200, {"drafts": drafts}, origin)
            return

        if parsed.path == "/api/posts":
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            if not self.server.publisher.configured:
                cached = self.server.store.list_cached_published_posts()
                if cached:
                    self._send_json(200, {"posts": cached, "source": "cache"}, origin)
                else:
                    self._send_json(503, {"error": "GitHub publishing is not configured."}, origin)
                return
            try:
                posts = self.server.publisher.list_posts()
                cached_by_file = {
                    item["filename"]: item
                    for item in self.server.store.list_cached_published_posts()
                    if isinstance(item, dict) and item.get("filename")
                }
                for post in posts:
                    cached = cached_by_file.get(post.get("filename", ""))
                    if cached:
                        if cached.get("title"):
                            post["title"] = cached["title"]
                        if cached.get("date"):
                            post["date"] = cached["date"]
                        if not post.get("html_url") and cached.get("html_url"):
                            post["html_url"] = cached["html_url"]
                self._send_json(200, {"posts": posts, "source": "github"}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(502, {"error": str(exc)}, origin)
            return

        draft_id = self._draft_id_from_path()
        if draft_id is not None:
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            draft = self.server.store.get_draft(draft_id)
            if draft is None:
                self._send_json(404, {"error": "Draft not found"}, origin)
                return
            self._send_json(200, {"draft": draft}, origin)
            return

        filename = self._post_filename_from_path()
        if filename is not None:
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            if not self.server.publisher.configured:
                self._send_json(503, {"error": "GitHub publishing is not configured."}, origin)
                return
            try:
                post = self.server.publisher.load_post(filename)
            except Exception as exc:  # noqa: BLE001
                self._send_json(502, {"error": str(exc)}, origin)
                return
            if post is None:
                self._send_json(404, {"error": "Post not found"}, origin)
                return
            self.server.store.upsert_published_post(post)
            self._send_json(200, {"post": post}, origin)
            return

        self._send_json(404, {"error": "Not found"}, origin)

    def do_POST(self) -> None:
        origin = self.headers.get("Origin")
        parsed = urllib.parse.urlparse(self.path)

        if parsed.path == "/api/session":
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
            return

        if parsed.path == "/api/publish":
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            if not self.server.publisher.configured:
                self._send_json(503, {"error": "GitHub publishing is not configured."}, origin)
                return

            try:
                payload = self._read_json()
            except Exception as exc:  # noqa: BLE001
                self._send_json(400, {"error": f"Invalid JSON payload: {exc}"}, origin)
                return

            title = str(payload.get("title", "")).strip()
            post_date = str(payload.get("date", "")).strip() or today_utc_date()
            body = str(payload.get("body", ""))
            filename = str(payload.get("filename", "")).strip()
            source_draft_id = str(payload.get("source_draft_id", "")).strip()

            if not title:
                self._send_json(400, {"error": "Title is required."}, origin)
                return
            if not body.strip():
                self._send_json(400, {"error": "Markdown body is required."}, origin)
                return
            if not DATE_RE.match(post_date):
                self._send_json(400, {"error": "Date must be YYYY-MM-DD."}, origin)
                return

            try:
                post = self.server.publisher.publish_post(
                    title=title,
                    post_date=post_date,
                    body=body,
                    requested_filename=filename,
                )
                self.server.store.upsert_published_post(post)
                if source_draft_id:
                    self.server.store.upsert_draft(
                        source_draft_id,
                        {
                            "title": post["title"],
                            "date": post["date"],
                            "body": post["body"],
                            "filename": post["filename"],
                            "markdown": post["markdown"],
                            "source_post_filename": post["filename"],
                        },
                    )
                self._send_json(200, {"post": post}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(502, {"error": str(exc)}, origin)
            return

        self._send_json(404, {"error": "Not found"}, origin)

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

        draft = self.server.store.upsert_draft(draft_id, payload)
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

    github_token = os.getenv("DRAFT_DB_GITHUB_TOKEN", "").strip()
    github_repo = os.getenv("DRAFT_DB_GITHUB_REPO", "").strip()
    github_branch = os.getenv("DRAFT_DB_GITHUB_BRANCH", "master").strip() or "master"
    github_timeout_seconds = int(os.getenv("DRAFT_DB_GITHUB_TIMEOUT_SECONDS", "20"))
    if bool(github_token) ^ bool(github_repo):
        raise SystemExit("Set both DRAFT_DB_GITHUB_TOKEN and DRAFT_DB_GITHUB_REPO, or set neither.")
    publisher = GitHubPublisher(
        token=github_token,
        repo=github_repo,
        branch=github_branch,
        timeout_seconds=github_timeout_seconds,
    )

    db_path = Path(args.db).expanduser().resolve()
    db_path.parent.mkdir(parents=True, exist_ok=True)
    store = DraftStore(db_path)
    allowed_origins = parse_allowed_origins(args.origins)

    server = DraftApiServer(
        (args.host, args.port),
        DraftApiHandler,
        store,
        auth_manager,
        allowed_origins,
        publisher,
    )
    print(
        f"Draft API listening on http://{args.host}:{args.port} "
        f"(db={db_path}, origins={sorted(allowed_origins)}, session_auth={auth_manager.supports_session}, "
        f"github_publish={publisher.configured}, github_repo={publisher.repo}, github_branch={publisher.branch})"
    )
    server.serve_forever()


if __name__ == "__main__":
    main()
