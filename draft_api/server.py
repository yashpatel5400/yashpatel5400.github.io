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
import secrets
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
PREVIEW_ID_RE = re.compile(r"^[A-Za-z0-9_-]{16,120}$")
DEFAULT_AUTOSAVE_HISTORY_LIMIT = 250
DEFAULT_PREVIEW_TTL_SECONDS = 14 * 24 * 60 * 60
MAX_PREVIEW_COMMENTER_LENGTH = 80
MAX_PREVIEW_COMMENT_LENGTH = 2000
MAX_PREVIEW_QUOTE_LENGTH = 600
MAX_PREVIEW_COMMENTS_PER_LINK = 500


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def today_utc_date() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def epoch_utc_iso(ts: int) -> str:
    return datetime.fromtimestamp(int(ts), timezone.utc).isoformat()


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
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS draft_autosaves (
                  autosave_id INTEGER PRIMARY KEY AUTOINCREMENT,
                  draft_id TEXT NOT NULL,
                  title TEXT NOT NULL DEFAULT '',
                  draft_date TEXT NOT NULL DEFAULT '',
                  body TEXT NOT NULL DEFAULT '',
                  filename TEXT NOT NULL DEFAULT '',
                  markdown TEXT NOT NULL DEFAULT '',
                  source_post_filename TEXT NOT NULL DEFAULT '',
                  saved_at TEXT NOT NULL
                )
                """
            )
            self._conn.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_draft_autosaves_draft_saved
                ON draft_autosaves (draft_id, autosave_id DESC)
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS shared_previews (
                  preview_id TEXT PRIMARY KEY,
                  title TEXT NOT NULL DEFAULT '',
                  post_date TEXT NOT NULL DEFAULT '',
                  body TEXT NOT NULL DEFAULT '',
                  created_at TEXT NOT NULL,
                  expires_at INTEGER NOT NULL
                )
                """
            )
            self._conn.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_shared_previews_expires
                ON shared_previews (expires_at)
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS shared_preview_comments (
                  comment_id INTEGER PRIMARY KEY AUTOINCREMENT,
                  preview_id TEXT NOT NULL,
                  start_offset INTEGER NOT NULL DEFAULT 0,
                  end_offset INTEGER NOT NULL DEFAULT 0,
                  quote TEXT NOT NULL DEFAULT '',
                  commenter TEXT NOT NULL DEFAULT '',
                  comment_text TEXT NOT NULL DEFAULT '',
                  delete_token_hash TEXT NOT NULL DEFAULT '',
                  created_at TEXT NOT NULL
                )
                """
            )
            self._conn.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_shared_preview_comments_preview
                ON shared_preview_comments (preview_id, comment_id ASC)
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

            comment_columns = {
                row["name"]
                for row in self._conn.execute(
                    "PRAGMA table_info(shared_preview_comments)"
                ).fetchall()
            }
            if "delete_token_hash" not in comment_columns:
                self._conn.execute(
                    "ALTER TABLE shared_preview_comments ADD COLUMN delete_token_hash TEXT NOT NULL DEFAULT ''"
                )

            self._conn.commit()

    @staticmethod
    def _normalize_draft_payload(payload: dict[str, Any]) -> dict[str, str]:
        title = str(payload.get("title", "")).strip()
        draft_date = str(payload.get("date", "")).strip() or today_utc_date()
        body = str(payload.get("body", ""))
        filename = str(payload.get("filename", "")).strip()
        markdown = str(payload.get("markdown", ""))
        source_post_filename = str(payload.get("source_post_filename", "")).strip()

        if not filename and title:
            filename = f"{draft_date}-{slugify(title)}.md"
        if not markdown and title:
            markdown = build_markdown(title, draft_date, body)

        return {
            "title": title,
            "draft_date": draft_date,
            "body": body,
            "filename": filename,
            "markdown": markdown,
            "source_post_filename": source_post_filename,
        }

    def _upsert_draft_locked(
        self,
        draft_id: str,
        fields: dict[str, str],
        updated_at: str,
    ) -> None:
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
                fields["title"],
                fields["draft_date"],
                fields["body"],
                fields["filename"],
                fields["markdown"],
                fields["source_post_filename"],
                updated_at,
            ),
        )

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
        fields = self._normalize_draft_payload(payload)
        updated_at = now_utc_iso()

        with self._lock:
            self._upsert_draft_locked(draft_id, fields, updated_at)
            self._conn.commit()

        return {
            "draft_id": draft_id,
            "title": fields["title"],
            "draft_date": fields["draft_date"],
            "body": fields["body"],
            "filename": fields["filename"],
            "markdown": fields["markdown"],
            "source_post_filename": fields["source_post_filename"],
            "updated_at": updated_at,
        }

    def delete_draft(self, draft_id: str) -> bool:
        with self._lock:
            deleted = self._conn.execute(
                "DELETE FROM drafts WHERE draft_id = ?",
                (draft_id,),
            ).rowcount
            self._conn.execute(
                "DELETE FROM draft_autosaves WHERE draft_id = ?",
                (draft_id,),
            )
            self._conn.commit()
        return deleted > 0

    def list_autosaves(self, draft_id: str, limit: int = 100) -> list[dict[str, Any]]:
        with self._lock:
            rows = self._conn.execute(
                """
                SELECT autosave_id, draft_id, title, draft_date, filename, source_post_filename, saved_at
                FROM draft_autosaves
                WHERE draft_id = ?
                ORDER BY autosave_id DESC
                LIMIT ?
                """,
                (draft_id, max(1, int(limit))),
            ).fetchall()
        return [dict(row) for row in rows]

    def get_autosave(self, draft_id: str, autosave_id: int) -> dict[str, Any] | None:
        with self._lock:
            row = self._conn.execute(
                """
                SELECT autosave_id, draft_id, title, draft_date, body, filename, markdown, source_post_filename, saved_at
                FROM draft_autosaves
                WHERE draft_id = ? AND autosave_id = ?
                """,
                (draft_id, int(autosave_id)),
            ).fetchone()
        if row is None:
            return None
        return dict(row)

    def create_autosave(
        self,
        draft_id: str,
        payload: dict[str, Any],
        keep_latest: int = DEFAULT_AUTOSAVE_HISTORY_LIMIT,
    ) -> dict[str, Any]:
        fields = self._normalize_draft_payload(payload)
        saved_at = now_utc_iso()
        keep_limit = max(25, int(keep_latest))

        with self._lock:
            self._upsert_draft_locked(draft_id, fields, saved_at)
            cursor = self._conn.execute(
                """
                INSERT INTO draft_autosaves (
                  draft_id, title, draft_date, body, filename, markdown, source_post_filename, saved_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    draft_id,
                    fields["title"],
                    fields["draft_date"],
                    fields["body"],
                    fields["filename"],
                    fields["markdown"],
                    fields["source_post_filename"],
                    saved_at,
                ),
            )
            autosave_id = int(cursor.lastrowid or 0)
            self._conn.execute(
                """
                DELETE FROM draft_autosaves
                WHERE draft_id = ?
                  AND autosave_id NOT IN (
                    SELECT autosave_id
                    FROM draft_autosaves
                    WHERE draft_id = ?
                    ORDER BY autosave_id DESC
                    LIMIT ?
                  )
                """,
                (draft_id, draft_id, keep_limit),
            )
            self._conn.commit()

        return {
            "autosave_id": autosave_id,
            "draft_id": draft_id,
            "title": fields["title"],
            "draft_date": fields["draft_date"],
            "filename": fields["filename"],
            "source_post_filename": fields["source_post_filename"],
            "saved_at": saved_at,
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

    def delete_cached_published_post(self, filename: str) -> bool:
        with self._lock:
            deleted = self._conn.execute(
                "DELETE FROM published_posts WHERE filename = ?",
                (filename,),
            ).rowcount
            self._conn.execute(
                "UPDATE drafts SET source_post_filename = '' WHERE source_post_filename = ?",
                (filename,),
            )
            self._conn.commit()
        return deleted > 0

    def _purge_expired_previews_locked(self, now_ts: int | None = None) -> None:
        cutoff = int(now_ts if now_ts is not None else time.time())
        self._conn.execute("DELETE FROM shared_previews WHERE expires_at <= ?", (cutoff,))
        self._conn.execute(
            """
            DELETE FROM shared_preview_comments
            WHERE preview_id NOT IN (SELECT preview_id FROM shared_previews)
            """
        )

    def create_shared_preview(
        self,
        payload: dict[str, Any],
        ttl_seconds: int = DEFAULT_PREVIEW_TTL_SECONDS,
    ) -> dict[str, Any]:
        title = str(payload.get("title", "")).strip() or "Untitled Draft"
        post_date = str(payload.get("date", "")).strip() or today_utc_date()
        if not DATE_RE.match(post_date):
            post_date = today_utc_date()
        body = str(payload.get("body", ""))
        created_at = now_utc_iso()
        expires_at = int(time.time()) + max(3600, int(ttl_seconds))

        preview_id = ""
        with self._lock:
            self._purge_expired_previews_locked()
            for _ in range(8):
                candidate = secrets.token_urlsafe(18)
                try:
                    self._conn.execute(
                        """
                        INSERT INTO shared_previews (
                          preview_id, title, post_date, body, created_at, expires_at
                        )
                        VALUES (?, ?, ?, ?, ?, ?)
                        """,
                        (candidate, title, post_date, body, created_at, expires_at),
                    )
                    preview_id = candidate
                    break
                except sqlite3.IntegrityError:
                    continue
            if not preview_id:
                raise RuntimeError("Unable to allocate preview id.")
            self._conn.commit()

        return {
            "preview_id": preview_id,
            "title": title,
            "date": post_date,
            "body": body,
            "created_at": created_at,
            "expires_at": epoch_utc_iso(expires_at),
        }

    def get_shared_preview(self, preview_id: str) -> dict[str, Any] | None:
        now_ts = int(time.time())
        with self._lock:
            self._purge_expired_previews_locked(now_ts)
            row = self._conn.execute(
                """
                SELECT preview_id, title, post_date AS date, body, created_at, expires_at
                FROM shared_previews
                WHERE preview_id = ? AND expires_at > ?
                """,
                (preview_id, now_ts),
            ).fetchone()
            self._conn.commit()
        if row is None:
            return None
        payload = dict(row)
        payload["expires_at"] = epoch_utc_iso(int(payload.get("expires_at", now_ts)))
        return payload

    def list_shared_preview_comments(
        self,
        preview_id: str,
        limit: int = MAX_PREVIEW_COMMENTS_PER_LINK,
    ) -> list[dict[str, Any]]:
        with self._lock:
            self._purge_expired_previews_locked()
            rows = self._conn.execute(
                """
                SELECT comment_id, preview_id, start_offset, end_offset, quote,
                       commenter, comment_text AS comment, created_at
                FROM shared_preview_comments
                WHERE preview_id = ?
                ORDER BY comment_id ASC
                LIMIT ?
                """,
                (preview_id, max(1, min(MAX_PREVIEW_COMMENTS_PER_LINK, int(limit)))),
            ).fetchall()
            self._conn.commit()
        return [dict(row) for row in rows]

    def create_shared_preview_comment(
        self,
        preview_id: str,
        payload: dict[str, Any],
    ) -> dict[str, Any]:
        start_offset = int(payload.get("start_offset", -1))
        end_offset = int(payload.get("end_offset", -1))
        if start_offset < 0 or end_offset <= start_offset:
            raise ValueError("Invalid highlighted text range.")

        quote = str(payload.get("quote", "")).strip()
        if not quote:
            raise ValueError("Highlighted quote is required.")
        if len(quote) > MAX_PREVIEW_QUOTE_LENGTH:
            quote = quote[:MAX_PREVIEW_QUOTE_LENGTH].rstrip()

        commenter = str(payload.get("commenter", "")).strip() or "Anonymous"
        if len(commenter) > MAX_PREVIEW_COMMENTER_LENGTH:
            commenter = commenter[:MAX_PREVIEW_COMMENTER_LENGTH].rstrip()

        comment_text = str(payload.get("comment", "")).strip()
        if not comment_text:
            comment_text = str(payload.get("comment_text", "")).strip()
        if not comment_text:
            raise ValueError("Comment text is required.")
        if len(comment_text) > MAX_PREVIEW_COMMENT_LENGTH:
            raise ValueError(
                f"Comment is too long (max {MAX_PREVIEW_COMMENT_LENGTH} characters)."
            )

        created_at = now_utc_iso()
        delete_token = secrets.token_urlsafe(20)
        delete_token_hash = hashlib.sha256(delete_token.encode("utf-8")).hexdigest()
        now_ts = int(time.time())
        with self._lock:
            self._purge_expired_previews_locked(now_ts)

            preview_row = self._conn.execute(
                """
                SELECT preview_id
                FROM shared_previews
                WHERE preview_id = ? AND expires_at > ?
                """,
                (preview_id, now_ts),
            ).fetchone()
            if preview_row is None:
                raise KeyError("Preview not found")

            count_row = self._conn.execute(
                """
                SELECT COUNT(*) AS total
                FROM shared_preview_comments
                WHERE preview_id = ?
                """,
                (preview_id,),
            ).fetchone()
            total = int(count_row["total"] if count_row is not None else 0)
            if total >= MAX_PREVIEW_COMMENTS_PER_LINK:
                raise RuntimeError("Comment limit reached for this preview.")

            cursor = self._conn.execute(
                """
                INSERT INTO shared_preview_comments (
                  preview_id, start_offset, end_offset, quote, commenter, comment_text, delete_token_hash, created_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    preview_id,
                    start_offset,
                    end_offset,
                    quote,
                    commenter,
                    comment_text,
                    delete_token_hash,
                    created_at,
                ),
            )
            comment_id = int(cursor.lastrowid or 0)
            self._conn.commit()

        return {
            "comment_id": comment_id,
            "preview_id": preview_id,
            "start_offset": start_offset,
            "end_offset": end_offset,
            "quote": quote,
            "commenter": commenter,
            "comment": comment_text,
            "created_at": created_at,
            "delete_token": delete_token,
        }

    def delete_shared_preview_comment(
        self,
        preview_id: str,
        comment_id: int,
        delete_token: str,
    ) -> bool:
        token = str(delete_token or "").strip()
        if not token:
            raise ValueError("Delete token is required.")

        now_ts = int(time.time())
        token_hash = hashlib.sha256(token.encode("utf-8")).hexdigest()
        with self._lock:
            self._purge_expired_previews_locked(now_ts)
            preview_row = self._conn.execute(
                """
                SELECT preview_id
                FROM shared_previews
                WHERE preview_id = ? AND expires_at > ?
                """,
                (preview_id, now_ts),
            ).fetchone()
            if preview_row is None:
                raise KeyError("Preview not found")

            row = self._conn.execute(
                """
                SELECT delete_token_hash
                FROM shared_preview_comments
                WHERE preview_id = ? AND comment_id = ?
                """,
                (preview_id, int(comment_id)),
            ).fetchone()
            if row is None:
                raise KeyError("Comment not found")

            stored_hash = str(row["delete_token_hash"] or "").strip()
            if not stored_hash or not hmac.compare_digest(stored_hash, token_hash):
                raise PermissionError("Invalid delete token.")

            deleted = self._conn.execute(
                """
                DELETE FROM shared_preview_comments
                WHERE preview_id = ? AND comment_id = ?
                """,
                (preview_id, int(comment_id)),
            ).rowcount
            self._conn.commit()
        return bool(deleted)


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

    def delete_post(self, filename: str) -> bool:
        if not self.configured:
            raise RuntimeError("GitHub publishing is not configured.")
        if not SAFE_FILENAME_RE.match(filename):
            raise RuntimeError("Invalid post filename.")

        repo_path = f"_posts/{filename}"
        existing = self._read_file(repo_path)
        if existing is None:
            return False

        existing_sha = str(existing.get("sha", "")).strip()
        if not existing_sha:
            raise RuntimeError("Unable to delete post because GitHub SHA is missing.")

        payload: dict[str, Any] = {
            "message": f"Delete post: {filename}",
            "sha": existing_sha,
            "branch": self.branch,
        }
        status, response_payload = self._json_request(
            "DELETE",
            f"/repos/{self.repo}/contents/{urllib.parse.quote(repo_path, safe='/')}",
            payload=payload,
        )
        if status == 404:
            return False
        if status not in (200, 202) or not isinstance(response_payload, dict):
            raise RuntimeError(self._github_error(status, response_payload))
        return True


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
        preview_base_url: str,
        preview_site_base: str,
        preview_ttl_seconds: int,
    ) -> None:
        super().__init__(server_address, handler_class)
        self.store = store
        self.auth_manager = auth_manager
        self.allowed_origins = allowed_origins
        self.publisher = publisher
        self.preview_base_url = preview_base_url.strip().rstrip("/")
        self.preview_site_base = preview_site_base.strip().rstrip("/")
        self.preview_ttl_seconds = max(3600, int(preview_ttl_seconds))


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
        self.send_header("Access-Control-Allow-Methods", "GET, PUT, POST, DELETE, OPTIONS")

    def _send_html(self, status: int, html_content: str, origin: str | None = None) -> None:
        body = html_content.encode("utf-8")
        self.send_response(status)
        self._set_cors_headers(origin)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

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

    def _preview_id_from_path(self) -> str | None:
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/preview/"
        if not parsed.path.startswith(prefix):
            return None
        preview_id = urllib.parse.unquote(parsed.path[len(prefix) :].strip())
        if not preview_id or "/" in preview_id or not PREVIEW_ID_RE.match(preview_id):
            return None
        return preview_id

    def _preview_comments_id_from_path(self) -> str | None:
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/api/previews/"
        suffix = "/comments"
        path = parsed.path
        if not path.startswith(prefix) or not path.endswith(suffix):
            return None
        preview_id = urllib.parse.unquote(path[len(prefix) : -len(suffix)].strip("/"))
        if not preview_id or "/" in preview_id or not PREVIEW_ID_RE.match(preview_id):
            return None
        return preview_id

    def _preview_comment_delete_path(self) -> tuple[str, int] | None:
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/api/previews/"
        marker = "/comments/"
        path = parsed.path
        if not path.startswith(prefix) or marker not in path:
            return None
        remainder = path[len(prefix) :]
        preview_part, comment_part = remainder.split(marker, 1)
        preview_id = urllib.parse.unquote(preview_part.strip("/"))
        comment_id_text = urllib.parse.unquote(comment_part.strip("/"))
        if (
            not preview_id
            or "/" in preview_id
            or not PREVIEW_ID_RE.match(preview_id)
            or not comment_id_text.isdigit()
        ):
            return None
        comment_id = int(comment_id_text)
        if comment_id < 1:
            return None
        return preview_id, comment_id

    def _request_base_url(self) -> str:
        proto = (self.headers.get("X-Forwarded-Proto") or "http").split(",")[0].strip() or "http"
        host = (self.headers.get("Host") or "").strip()
        if not host:
            server_host, server_port = self.server.server_address
            host = f"{server_host}:{server_port}"
        return f"{proto}://{host}"

    def _resolved_preview_base_url(self) -> str:
        configured = self.server.preview_base_url
        if configured:
            return configured
        return self._request_base_url().rstrip("/")

    def _render_shared_preview_page(self, preview: dict[str, Any]) -> str:
        preview_id = str(preview.get("preview_id", "")).strip()
        title = str(preview.get("title", "")).strip() or "Untitled Draft"
        post_date = str(preview.get("date", "")).strip()
        body = str(preview.get("body", ""))
        site_base = self.server.preview_site_base or "https://ypatel.io"
        site_base = site_base.rstrip("/")
        payload_json = json.dumps(
            {"preview_id": preview_id, "title": title, "date": post_date, "body": body},
            ensure_ascii=False,
        ).replace("</", "<\\/")
        escaped_title = (
            title.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        )

        return f"""<!DOCTYPE html>
<html lang="en-US">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="robots" content="noindex,nofollow">
  <title>{escaped_title} (Shared Preview)</title>
  <link rel="stylesheet" href="{site_base}/assets/css/style.css">
  <link rel="stylesheet" href="{site_base}/static/css/custom.css">
  <style>
    .post-preview-banner {{
      margin: 0 0 0.8rem;
      border: 1px solid #d6e2f5;
      border-radius: 10px;
      background: #f4f8ff;
      color: #35557f;
      padding: 0.6rem 0.75rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.85rem;
    }}
    .blog-standalone .shared-preview-wrapper {{
      width: 100%;
      max-width: none !important;
      margin: 0;
      padding: 0 1.1rem 0 0.95rem;
      box-sizing: border-box;
    }}
    .blog-standalone .shared-preview-wrapper > section {{
      max-width: none;
      width: 100%;
      margin: 0;
    }}
    .shared-preview-layout {{
      display: grid;
      grid-template-columns: minmax(0, 1.6fr) minmax(340px, 1fr);
      gap: 1.3rem;
      align-items: start;
      position: relative;
    }}
    .shared-preview-layout .post-article {{
      max-width: none;
      width: 100%;
      margin: 0;
    }}
    .shared-preview-layout .post-body {{
      position: relative;
    }}
    .shared-preview-identity {{
      margin: 0 0 0.95rem;
      display: flex;
      align-items: center;
      gap: 0.55rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.84rem;
      font-weight: 600;
      color: #4b5c76;
      letter-spacing: 0.04em;
      text-transform: uppercase;
    }}
    .shared-preview-identity input {{
      min-width: 220px;
      max-width: 280px;
      border: 1px solid #cfd8ea;
      border-radius: 9px;
      padding: 0.45rem 0.6rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.95rem;
      letter-spacing: 0;
      text-transform: none;
      color: #1f2937;
      background: #fff;
    }}
    .shared-preview-identity input:focus {{
      outline: none;
      border-color: #3e6ddd;
      box-shadow: 0 0 0 3px rgba(76, 114, 211, 0.2);
    }}
    .shared-preview-comments-rail {{
      position: relative;
      border-left: 1px solid #dde3ef;
      padding-left: 1rem;
      min-height: 220px;
      min-width: 0;
    }}
    .shared-preview-comments-layer {{
      position: relative;
      min-height: 220px;
    }}
    .shared-preview-comments-empty {{
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.9rem;
      color: #6b7788;
    }}
    .shared-preview-comment-card {{
      position: absolute;
      left: 0;
      right: 0;
      border: 1px solid #d4dcec;
      border-radius: 12px;
      background: #f8faff;
      box-shadow: 0 8px 18px rgba(29, 52, 84, 0.08);
      padding: 0.65rem 0.7rem;
    }}
    .shared-preview-comment-meta-row {{
      margin: 0 0 0.3rem;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 0.5rem;
    }}
    .shared-preview-comment-meta {{
      margin: 0;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.8rem;
      font-weight: 600;
      color: #4f5f79;
    }}
    .shared-preview-comment-delete {{
      border: 0;
      background: transparent;
      color: #d14b4b;
      cursor: pointer;
      font-size: 0.8rem;
      font-weight: 700;
      letter-spacing: 0.02em;
      padding: 0.1rem 0.2rem;
      line-height: 1;
    }}
    .shared-preview-comment-delete:hover {{
      color: #ad2f2f;
    }}
    .shared-preview-comment-delete-confirm {{
      margin: 0.5rem 0 0;
      display: flex;
      align-items: center;
      flex-wrap: wrap;
      gap: 0.35rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.78rem;
      color: #53627b;
    }}
    .shared-preview-comment-delete-confirm button {{
      border: 0;
      border-radius: 999px;
      padding: 0.28rem 0.58rem;
      cursor: pointer;
      font-size: 0.76rem;
      font-weight: 700;
      letter-spacing: 0.02em;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
    }}
    .shared-preview-comment-delete-confirm [data-delete-confirm] {{
      background: #d14b4b;
      color: #fff;
    }}
    .shared-preview-comment-delete-confirm [data-delete-cancel] {{
      background: #e6ebf5;
      color: #455369;
    }}
    .shared-preview-comment-delete-confirm button[disabled] {{
      opacity: 0.72;
      cursor: default;
    }}
    .shared-preview-comment-quote {{
      margin: 0 0 0.35rem;
      padding: 0.25rem 0.45rem;
      border-left: 3px solid #4f7fe3;
      border-radius: 6px;
      background: #eaf0ff;
      font-size: 0.83rem;
      color: #3f5069;
    }}
    .shared-preview-comment-body {{
      margin: 0;
      font-size: 0.92rem;
      line-height: 1.45;
      color: #1f2937;
      white-space: pre-wrap;
      word-break: break-word;
    }}
    .shared-preview-comment-compose textarea {{
      width: 100%;
      max-width: 100%;
      box-sizing: border-box;
      min-height: 84px;
      resize: vertical;
      border: 1px solid #cbd6eb;
      border-radius: 8px;
      background: #fff;
      color: #111827;
      font-size: 0.92rem;
      line-height: 1.45;
      padding: 0.5rem 0.55rem;
      margin: 0 0 0.55rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
    }}
    .shared-preview-comment-compose textarea:focus {{
      outline: none;
      border-color: #3e6ddd;
      box-shadow: 0 0 0 3px rgba(76, 114, 211, 0.2);
    }}
    .shared-preview-comment-compose-actions {{
      display: flex;
      align-items: center;
      gap: 0.45rem;
      margin: 0 0 0.2rem;
    }}
    .shared-preview-comment-compose-actions button {{
      border: 0;
      border-radius: 999px;
      padding: 0.35rem 0.65rem;
      cursor: pointer;
      font-size: 0.8rem;
      font-weight: 700;
      letter-spacing: 0.02em;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
    }}
    .shared-preview-comment-compose-actions [data-comment-save] {{
      background: #2f5bd3;
      color: #fff;
    }}
    .shared-preview-comment-compose-actions [data-comment-save][disabled] {{
      opacity: 0.72;
      cursor: default;
    }}
    .shared-preview-comment-compose-actions [data-comment-cancel] {{
      background: #e6ebf5;
      color: #455369;
    }}
    .shared-preview-comment-compose-error {{
      margin: 0;
      min-height: 1.1rem;
      color: #c23a3a;
      font-size: 0.78rem;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
    }}
    .shared-preview-comment-trigger {{
      position: fixed;
      z-index: 3000;
      border: 0;
      border-radius: 999px;
      background: #2f5bd3;
      color: #fff;
      font-family: "Space Grotesk", -apple-system, "Segoe UI", sans-serif;
      font-size: 0.82rem;
      font-weight: 700;
      letter-spacing: 0.02em;
      padding: 0.4rem 0.65rem;
      cursor: pointer;
      box-shadow: 0 10px 26px rgba(34, 69, 148, 0.28);
    }}
    .shared-preview-comment-trigger[disabled] {{
      opacity: 0.75;
      cursor: default;
    }}
    .shared-preview-highlight-layer {{
      position: absolute;
      inset: 0;
      pointer-events: none;
      z-index: 2;
      overflow: hidden;
    }}
    .shared-preview-highlight-rect {{
      position: absolute;
      border-radius: 3px;
      background: rgba(69, 108, 214, 0.18);
    }}
    .shared-preview-highlight-rect.is-draft {{
      background: rgba(69, 108, 214, 0.29);
    }}
    ::highlight(shared-preview-commented) {{
      background: rgba(69, 108, 214, 0.2);
      color: inherit;
    }}
    ::highlight(shared-preview-draft) {{
      background: rgba(69, 108, 214, 0.3);
      color: inherit;
    }}
    @media (max-width: 980px) {{
      .shared-preview-layout {{
        grid-template-columns: minmax(0, 1fr);
      }}
      .blog-standalone .shared-preview-wrapper {{
        padding-left: 0.8rem;
        padding-right: 0.8rem;
      }}
      .shared-preview-identity input {{
        min-width: 170px;
        width: 100%;
        max-width: 100%;
      }}
      .shared-preview-comments-rail {{
        border-left: 0;
        border-top: 1px solid #dde3ef;
        padding-left: 0;
        padding-top: 0.85rem;
      }}
      .shared-preview-comment-card {{
        position: relative;
        top: auto !important;
        margin-bottom: 0.65rem;
      }}
    }}
  </style>
</head>
<body class="blog-standalone">
  <div class="wrapper shared-preview-wrapper">
    <section>
      <p class="post-preview-banner">Shared draft preview. Highlight text and click <strong>Leave a comment</strong>.</p>
      <div class="shared-preview-layout" id="preview-layout">
        <article class="post-article" id="preview-article">
          <div class="shared-preview-identity">
            <label for="preview-commenter-name">Name</label>
            <input id="preview-commenter-name" type="text" maxlength="80" placeholder="Your name">
          </div>
          <p class="post-breadcrumb"><a href="{site_base}/blog/">&larr; Back to Blog</a></p>
          <h2 class="post-title">{escaped_title}</h2>
          <p class="post-date" id="preview-post-date"></p>
          <div class="post-content" id="preview-post-body"></div>
        </article>
        <aside class="shared-preview-comments-rail">
          <div class="shared-preview-comments-layer" id="preview-comments-layer"></div>
          <p class="shared-preview-comments-empty" id="preview-comments-empty">No comments yet. Select text to leave one.</p>
        </aside>
      </div>
    </section>
  </div>
  <button type="button" class="shared-preview-comment-trigger" id="preview-comment-trigger" hidden>Leave a comment</button>
  <script id="preview-payload" type="application/json">{payload_json}</script>
  <script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
  <script src="https://cdn.jsdelivr.net/npm/dompurify@3.1.6/dist/purify.min.js"></script>
  <script>
    (function() {{
      function escapeHtml(text) {{
        return String(text || '')
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;');
      }}
      function formatDateLabel(dateString) {{
        if (!dateString) return '';
        var parsed = new Date(dateString + 'T00:00:00');
        if (Number.isNaN(parsed.getTime())) return dateString;
        return parsed.toLocaleDateString(undefined, {{
          year: 'numeric',
          month: 'long',
          day: 'numeric'
        }});
      }}
      function renderMarkdown(raw) {{
        var text = String(raw || '');
        if (window.marked && typeof window.marked.parse === 'function') {{
          var parsed = window.marked.parse(text, {{
            gfm: true,
            breaks: true,
            mangle: false,
            headerIds: true
          }});
          if (window.DOMPurify && typeof window.DOMPurify.sanitize === 'function') {{
            return window.DOMPurify.sanitize(parsed, {{ USE_PROFILES: {{ html: true }} }});
          }}
          return parsed;
        }}
        return '<pre>' + escapeHtml(text) + '</pre>';
      }}
      function formatDateTimeLabel(value) {{
        if (!value) return '';
        var parsed = new Date(value);
        if (Number.isNaN(parsed.getTime())) return '';
        return parsed.toLocaleString(undefined, {{
          year: 'numeric',
          month: 'short',
          day: 'numeric',
          hour: 'numeric',
          minute: '2-digit'
        }});
      }}
      function collapseWhitespace(text) {{
        return String(text || '').replace(/\\s+/g, ' ').trim();
      }}
      function commenterStorageKey() {{
        return 'shared_preview_commenter_name';
      }}
      function commentTokenStorageKey() {{
        if (!previewId) return '';
        return 'shared_preview_comment_tokens:' + previewId;
      }}
      function loadCommenterName() {{
        try {{
          var value = window.localStorage ? window.localStorage.getItem(commenterStorageKey()) : '';
          return collapseWhitespace(value || '');
        }} catch (err) {{
          return '';
        }}
      }}
      function saveCommenterName(name) {{
        try {{
          if (window.localStorage) {{
            if (name) {{
              window.localStorage.setItem(commenterStorageKey(), name);
            }} else {{
              window.localStorage.removeItem(commenterStorageKey());
            }}
          }}
        }} catch (err) {{
          // Ignore storage failures.
        }}
      }}
      function currentCommenterName() {{
        var value = commenterNameEl ? collapseWhitespace(commenterNameEl.value || '') : '';
        return value || 'Anonymous';
      }}
      function loadDeleteTokens() {{
        var key = commentTokenStorageKey();
        if (!key) return {{}};
        try {{
          if (!window.localStorage) return {{}};
          var raw = window.localStorage.getItem(key);
          if (!raw) return {{}};
          var parsed = JSON.parse(raw);
          if (!parsed || typeof parsed !== 'object') return {{}};
          return parsed;
        }} catch (err) {{
          return {{}};
        }}
      }}
      function saveDeleteTokens() {{
        var key = commentTokenStorageKey();
        if (!key) return;
        try {{
          if (window.localStorage) {{
            window.localStorage.setItem(key, JSON.stringify(deleteTokens || {{}}));
          }}
        }} catch (err) {{
          // Ignore storage failures.
        }}
      }}
      function rememberDeleteToken(commentId, token) {{
        if (!commentId || !token) return;
        deleteTokens[String(commentId)] = String(token);
        saveDeleteTokens();
      }}
      function forgetDeleteToken(commentId) {{
        if (!commentId) return;
        delete deleteTokens[String(commentId)];
        saveDeleteTokens();
      }}

      var payloadEl = document.getElementById('preview-payload');
      var payload = {{}};
      try {{
        payload = JSON.parse(payloadEl && payloadEl.textContent ? payloadEl.textContent : '{{}}');
      }} catch (err) {{
        payload = {{}};
      }}

      var previewId = payload.preview_id ? String(payload.preview_id) : '';
      var layoutEl = document.getElementById('preview-layout');
      var articleEl = document.getElementById('preview-article');
      var dateEl = document.getElementById('preview-post-date');
      var bodyEl = document.getElementById('preview-post-body');
      var commenterNameEl = document.getElementById('preview-commenter-name');
      var commentsLayerEl = document.getElementById('preview-comments-layer');
      var commentsEmptyEl = document.getElementById('preview-comments-empty');
      var commentTriggerEl = document.getElementById('preview-comment-trigger');
      var activeSelection = null;
      var draftComment = null;
      var comments = [];
      var deleteTokens = {{}};
      var deletingCommentIds = {{}};
      var pendingDeleteCommentId = '';
      var deleteErrors = {{}};
      var renderTimer = null;

      function hideCommentTrigger() {{
        activeSelection = null;
        if (!commentTriggerEl) return;
        commentTriggerEl.hidden = true;
        commentTriggerEl.disabled = false;
        commentTriggerEl.textContent = 'Leave a comment';
      }}

      function clearSelectionRange() {{
        var sel = window.getSelection && window.getSelection();
        if (sel && typeof sel.removeAllRanges === 'function') {{
          try {{
            sel.removeAllRanges();
          }} catch (err) {{
            // Ignore browser selection errors.
          }}
        }}
      }}

      function getSelectionOffsets(range) {{
        if (!bodyEl || !range) return null;
        var beforeStart = document.createRange();
        var beforeEnd = document.createRange();
        beforeStart.selectNodeContents(bodyEl);
        beforeStart.setEnd(range.startContainer, range.startOffset);
        beforeEnd.selectNodeContents(bodyEl);
        beforeEnd.setEnd(range.endContainer, range.endOffset);
        var startOffset = beforeStart.toString().length;
        var endOffset = beforeEnd.toString().length;
        if (!Number.isFinite(startOffset) || !Number.isFinite(endOffset) || endOffset <= startOffset) {{
          return null;
        }}
        return {{ start_offset: startOffset, end_offset: endOffset }};
      }}

      function getSelectionPayload() {{
        if (!bodyEl) return null;
        var sel = window.getSelection && window.getSelection();
        if (!sel || sel.rangeCount < 1 || sel.isCollapsed) return null;
        var range = sel.getRangeAt(0);
        if (!range || !bodyEl.contains(range.commonAncestorContainer)) return null;
        var quote = collapseWhitespace(range.toString());
        if (!quote) return null;
        var offsets = getSelectionOffsets(range);
        if (!offsets) return null;
        var rect = range.getBoundingClientRect();
        if (!rect || (!rect.width && !rect.height)) return null;
        return {{
          start_offset: offsets.start_offset,
          end_offset: offsets.end_offset,
          quote: quote,
          rect: rect
        }};
      }}

      function placeCommentTrigger(rect) {{
        if (!commentTriggerEl || !rect) return;
        var left = rect.left + (rect.width / 2) - 58;
        var top = rect.bottom + 10;
        var minLeft = 8;
        var maxLeft = window.innerWidth - 132;
        if (left < minLeft) left = minLeft;
        if (left > maxLeft) left = maxLeft;
        commentTriggerEl.style.left = String(Math.round(left)) + 'px';
        commentTriggerEl.style.top = String(Math.round(top)) + 'px';
        commentTriggerEl.hidden = false;
      }}

      function computeRangeFromOffsets(startOffset, endOffset) {{
        if (!bodyEl) return null;
        if (!Number.isFinite(startOffset) || !Number.isFinite(endOffset) || endOffset <= startOffset) {{
          return null;
        }}
        var walker = document.createTreeWalker(bodyEl, NodeFilter.SHOW_TEXT);
        var currentOffset = 0;
        var startNode = null;
        var endNode = null;
        var startNodeOffset = 0;
        var endNodeOffset = 0;
        var node = walker.nextNode();
        while (node) {{
          var textLength = node.nodeValue ? node.nodeValue.length : 0;
          var nextOffset = currentOffset + textLength;

          if (!startNode && startOffset >= currentOffset && startOffset <= nextOffset) {{
            startNode = node;
            startNodeOffset = startOffset - currentOffset;
          }}
          if (!endNode && endOffset >= currentOffset && endOffset <= nextOffset) {{
            endNode = node;
            endNodeOffset = endOffset - currentOffset;
          }}

          if (startNode && endNode) {{
            break;
          }}
          currentOffset = nextOffset;
          node = walker.nextNode();
        }}

        if (!startNode || !endNode) return null;
        var range = document.createRange();
        range.setStart(startNode, startNodeOffset);
        range.setEnd(endNode, endNodeOffset);
        return range;
      }}

      function ensureHighlightLayer() {{
        if (!bodyEl) return null;
        var layer = bodyEl.querySelector('[data-preview-highlight-layer]');
        if (!layer) {{
          layer = document.createElement('div');
          layer.className = 'shared-preview-highlight-layer';
          layer.setAttribute('data-preview-highlight-layer', '1');
          bodyEl.insertBefore(layer, bodyEl.firstChild);
        }}
        return layer;
      }}

      function addHighlightRects(layer, range, className, baseRect) {{
        if (!layer || !range || !baseRect) return;
        var rects = range.getClientRects();
        for (var i = 0; i < rects.length; i += 1) {{
          var rect = rects[i];
          if (!rect || rect.width < 1 || rect.height < 1) {{
            continue;
          }}
          var chip = document.createElement('span');
          chip.className = 'shared-preview-highlight-rect' + (className ? ' ' + className : '');
          chip.style.left = String(rect.left - baseRect.left) + 'px';
          chip.style.top = String(rect.top - baseRect.top) + 'px';
          chip.style.width = String(rect.width) + 'px';
          chip.style.height = String(rect.height) + 'px';
          layer.appendChild(chip);
        }}
      }}

      function renderHighlightOverlay(commentRanges, draftRange) {{
        var layer = ensureHighlightLayer();
        if (!layer || !bodyEl) return;
        layer.innerHTML = '';
        layer.style.minHeight = String(Math.max(bodyEl.scrollHeight, bodyEl.clientHeight, 0)) + 'px';

        var bodyRect = bodyEl.getBoundingClientRect();
        for (var i = 0; i < commentRanges.length; i += 1) {{
          addHighlightRects(layer, commentRanges[i], '', bodyRect);
        }}
        if (draftRange) {{
          addHighlightRects(layer, draftRange, 'is-draft', bodyRect);
        }}
      }}

      function clearHighlightOverlay() {{
        if (!bodyEl) return;
        var layer = bodyEl.querySelector('[data-preview-highlight-layer]');
        if (layer) {{
          layer.innerHTML = '';
        }}
      }}

      function getCommentAnchorTop(comment) {{
        if (!layoutEl) return null;
        var startOffset = Number(comment.start_offset);
        var endOffset = Number(comment.end_offset);
        var range = computeRangeFromOffsets(startOffset, endOffset);
        if (!range) return null;
        var rect = range.getBoundingClientRect();
        if (!rect || (!rect.width && !rect.height)) return null;
        var layoutRect = layoutEl.getBoundingClientRect();
        return rect.top - layoutRect.top;
      }}

      function queueCommentRender() {{
        if (renderTimer) {{
          window.clearTimeout(renderTimer);
        }}
        renderTimer = window.setTimeout(renderComments, 50);
      }}

      function renderCommentHighlights(orderedComments) {{
        var list = Array.isArray(orderedComments) ? orderedComments : [];
        var commentRanges = [];
        for (var i = 0; i < list.length; i += 1) {{
          var comment = list[i];
          var range = computeRangeFromOffsets(
            Number(comment && comment.start_offset),
            Number(comment && comment.end_offset)
          );
          if (range) {{
            commentRanges.push(range);
          }}
        }}

        var draftRange = null;
        if (draftComment && draftComment.selection) {{
          draftRange = computeRangeFromOffsets(
            Number(draftComment.selection.start_offset),
            Number(draftComment.selection.end_offset)
          );
        }}

        var hasCssHighlightApi = !!(
          window.CSS &&
          window.CSS.highlights &&
          typeof window.Highlight === 'function'
        );
        if (!hasCssHighlightApi) {{
          renderHighlightOverlay(commentRanges, draftRange);
          return;
        }}

        clearHighlightOverlay();
        try {{
          window.CSS.highlights.delete('shared-preview-commented');
          window.CSS.highlights.delete('shared-preview-draft');
          if (commentRanges.length > 0) {{
            var commentedHighlight = new window.Highlight();
            for (var j = 0; j < commentRanges.length; j += 1) {{
              commentedHighlight.add(commentRanges[j]);
            }}
            window.CSS.highlights.set('shared-preview-commented', commentedHighlight);
          }}
          if (draftRange) {{
            var draftHighlight = new window.Highlight();
            draftHighlight.add(draftRange);
            window.CSS.highlights.set('shared-preview-draft', draftHighlight);
          }}
        }} catch (err) {{
          // Fallback for browsers with partial/buggy Highlight API behavior.
          renderHighlightOverlay(commentRanges, draftRange);
        }}
      }}

      function renderComments() {{
        if (!commentsLayerEl) return;
        commentsLayerEl.innerHTML = '';

        var minHeight = articleEl ? Math.max(articleEl.offsetHeight, 240) : 240;
        commentsLayerEl.style.minHeight = String(minHeight) + 'px';

        var ordered = comments.slice().map(function(comment) {{
          return {{
            comment: comment,
            anchorTop: getCommentAnchorTop(comment)
          }};
        }});
        ordered.sort(function(a, b) {{
          var aTop = a.anchorTop;
          var bTop = b.anchorTop;
          var aHasTop = aTop !== null && Number.isFinite(aTop);
          var bHasTop = bTop !== null && Number.isFinite(bTop);
          if (aHasTop && bHasTop) {{
            if (Math.abs(aTop - bTop) > 0.5) {{
              return aTop - bTop;
            }}
          }} else if (aHasTop) {{
            return -1;
          }} else if (bHasTop) {{
            return 1;
          }}
          return Number((a.comment && a.comment.comment_id) || 0) - Number((b.comment && b.comment.comment_id) || 0);
        }});

        var orderedComments = ordered.map(function(entry) {{
          return entry.comment;
        }});
        renderCommentHighlights(orderedComments);
        var floor = 0;
        var draftComposeBottom = 0;

        if ((!orderedComments || orderedComments.length < 1) && !draftComment) {{
          if (commentsEmptyEl) commentsEmptyEl.style.display = 'block';
        }} else if (commentsEmptyEl) {{
          commentsEmptyEl.style.display = 'none';
        }}

        for (var idx = 0; idx < ordered.length; idx += 1) {{
          var entry = ordered[idx];
          var comment = entry.comment;
          var createdLabel = formatDateTimeLabel(comment.created_at || '');
          var commenter = collapseWhitespace(comment.commenter || '') || 'Anonymous';
          var quote = collapseWhitespace(comment.quote || '');
          var message = String(comment.comment || '').trim();
          var commentId = String(comment.comment_id || '');
          var hasDeleteToken = !!deleteTokens[commentId];
          var deleting = !!deletingCommentIds[commentId];
          var showingDeleteConfirm = hasDeleteToken && pendingDeleteCommentId === commentId;
          var deleteError = String(deleteErrors[commentId] || '').trim();
          if (!message) continue;

          var card = document.createElement('article');
          card.className = 'shared-preview-comment-card';
          card.innerHTML =
            '<div class="shared-preview-comment-meta-row">' +
              '<p class="shared-preview-comment-meta">' +
                escapeHtml(commenter) +
                (createdLabel ? ' \u00b7 ' + escapeHtml(createdLabel) : '') +
              '</p>' +
              (hasDeleteToken && !showingDeleteConfirm
                ? ('<button type="button" class="shared-preview-comment-delete" data-delete-comment="' + escapeHtml(commentId) + '"' + (deleting ? ' disabled' : '') + '>' + (deleting ? 'Deleting...' : 'Delete') + '</button>')
                : ''
              ) +
            '</div>' +
            (quote ? '<p class="shared-preview-comment-quote">\u201c' + escapeHtml(quote) + '\u201d</p>' : '') +
            '<p class="shared-preview-comment-body">' + escapeHtml(message) + '</p>' +
            (showingDeleteConfirm
              ? (
                '<div class="shared-preview-comment-delete-confirm">' +
                  '<span>Delete this comment?</span>' +
                  '<button type="button" data-delete-confirm="' + escapeHtml(commentId) + '"' + (deleting ? ' disabled' : '') + '>' + (deleting ? 'Deleting...' : 'Confirm') + '</button>' +
                  '<button type="button" data-delete-cancel="' + escapeHtml(commentId) + '"' + (deleting ? ' disabled' : '') + '>Cancel</button>' +
                '</div>'
              )
              : ''
            ) +
            (deleteError
              ? ('<p class="shared-preview-comment-compose-error">' + escapeHtml(deleteError) + '</p>')
              : ''
            );

          var top = floor;
          var anchorTop = entry.anchorTop;
          if (anchorTop !== null && Number.isFinite(anchorTop)) {{
            top = Math.max(floor, anchorTop - 8);
          }}
          card.style.top = String(Math.round(top)) + 'px';
          commentsLayerEl.appendChild(card);
          floor = top + card.offsetHeight + 12;
        }}

        if (draftComment) {{
          var draftQuote = collapseWhitespace(
            draftComment.selection && draftComment.selection.quote ? draftComment.selection.quote : ''
          );
          var draftAnchorTop = getCommentAnchorTop(draftComment.selection || null);
          var draftTop = floor;
          if (draftAnchorTop !== null && Number.isFinite(draftAnchorTop)) {{
            draftTop = Math.max(0, draftAnchorTop - 8);
          }}

          var composeCard = document.createElement('article');
          composeCard.className = 'shared-preview-comment-card shared-preview-comment-compose';
          composeCard.style.top = String(Math.round(draftTop)) + 'px';
          composeCard.innerHTML =
            '<div class="shared-preview-comment-meta-row">' +
              '<p class="shared-preview-comment-meta">' + escapeHtml(currentCommenterName()) + ' \u00b7 new comment</p>' +
            '</div>' +
            (draftQuote ? '<p class="shared-preview-comment-quote">\u201c' + escapeHtml(draftQuote) + '\u201d</p>' : '') +
            '<textarea data-compose-input placeholder="Type your comment..."></textarea>' +
            '<div class="shared-preview-comment-compose-actions">' +
              '<button type="button" data-comment-save>' + (draftComment.saving ? 'Saving...' : 'Save comment') + '</button>' +
              '<button type="button" data-comment-cancel>Cancel</button>' +
            '</div>' +
            '<p class="shared-preview-comment-compose-error">' +
              escapeHtml(draftComment.error || '') +
            '</p>';

          commentsLayerEl.appendChild(composeCard);
          draftComposeBottom = draftTop + composeCard.offsetHeight + 12;

          var composeTextarea = composeCard.querySelector('[data-compose-input]');
          var saveBtn = composeCard.querySelector('[data-comment-save]');
          if (composeTextarea) {{
            composeTextarea.value = draftComment.text || '';
            composeTextarea.disabled = !!draftComment.saving;
            composeTextarea.addEventListener('keydown', function(event) {{
              if (!isCommentSaveShortcut(event)) return;
              event.preventDefault();
              event.stopPropagation();
              saveInlineCommentDraft();
            }});
            if (draftComment.needsFocus && !draftComment.saving) {{
              composeTextarea.focus();
              composeTextarea.setSelectionRange(composeTextarea.value.length, composeTextarea.value.length);
              draftComment.needsFocus = false;
            }}
          }}
          if (saveBtn && draftComment.saving) {{
            saveBtn.disabled = true;
          }}
        }}

        var targetHeight = Math.max(minHeight, floor + 10, draftComposeBottom + 10);
        commentsLayerEl.style.minHeight = String(targetHeight) + 'px';
      }}

      function startInlineCommentDraft() {{
        if (!activeSelection) return;
        draftComment = {{
          selection: {{
            start_offset: activeSelection.start_offset,
            end_offset: activeSelection.end_offset,
            quote: activeSelection.quote
          }},
          text: '',
          error: '',
          saving: false,
          needsFocus: true
        }};
        clearSelectionRange();
        hideCommentTrigger();
        queueCommentRender();
      }}

      function cancelInlineCommentDraft() {{
        draftComment = null;
        queueCommentRender();
      }}

      function commentsEndpoint() {{
        if (!previewId) return '';
        return '/api/previews/' + encodeURIComponent(previewId) + '/comments';
      }}
      function commentDeleteEndpoint(commentId) {{
        if (!previewId || !commentId) return '';
        return '/api/previews/' + encodeURIComponent(previewId) + '/comments/' + encodeURIComponent(String(commentId));
      }}

      function fetchComments() {{
        var endpoint = commentsEndpoint();
        if (!endpoint) return Promise.resolve();
        return fetch(endpoint, {{
          method: 'GET',
          headers: {{ 'Accept': 'application/json' }}
        }})
          .then(function(response) {{
            if (!response.ok) {{
              throw new Error('Unable to load comments.');
            }}
            return response.json();
          }})
          .then(function(result) {{
            comments = result && Array.isArray(result.comments) ? result.comments : [];
            queueCommentRender();
          }})
          .catch(function() {{
            comments = [];
            queueCommentRender();
          }});
      }}

      function submitComment(selection, commentText, commenter) {{
        var endpoint = commentsEndpoint();
        if (!endpoint) return Promise.reject(new Error('Preview id unavailable.'));
        return fetch(endpoint, {{
          method: 'POST',
          headers: {{
            'Content-Type': 'application/json',
            'Accept': 'application/json'
          }},
          body: JSON.stringify({{
            start_offset: selection.start_offset,
            end_offset: selection.end_offset,
            quote: selection.quote,
            commenter: commenter,
            comment: commentText
          }})
        }})
          .then(function(response) {{
            return response.json().catch(function() {{ return {{}}; }}).then(function(result) {{
              if (!response.ok) {{
                var message = result && result.error ? String(result.error) : 'Unable to save comment.';
                throw new Error(message);
              }}
              return result;
            }});
          }})
          .then(function(result) {{
            if (!result || !result.comment) {{
              throw new Error('Comment save failed.');
            }}
            if (result.delete_token) {{
              rememberDeleteToken(result.comment.comment_id, result.delete_token);
            }}
            comments.push(result.comment);
            queueCommentRender();
            return result.comment;
          }});
      }}

      function deleteComment(commentId) {{
        var commentKey = String(commentId || '');
        var endpoint = commentDeleteEndpoint(commentKey);
        if (!endpoint) return Promise.reject(new Error('Invalid comment id.'));
        var token = deleteTokens[commentKey];
        if (!token) return Promise.reject(new Error('Delete permission not found for this comment.'));

        deletingCommentIds[commentKey] = true;
        deleteErrors[commentKey] = '';
        queueCommentRender();

        return fetch(endpoint, {{
          method: 'DELETE',
          headers: {{
            'Accept': 'application/json',
            'X-Comment-Delete-Token': String(token)
          }}
        }})
          .then(function(response) {{
            return response.json().catch(function() {{ return {{}}; }}).then(function(result) {{
              if (!response.ok) {{
                var message = result && result.error ? String(result.error) : 'Unable to delete comment.';
                throw new Error(message);
              }}
              return result;
            }});
          }})
          .then(function() {{
            comments = comments.filter(function(item) {{
              return String(item && item.comment_id) !== commentKey;
            }});
            forgetDeleteToken(commentKey);
            delete deletingCommentIds[commentKey];
            delete deleteErrors[commentKey];
            if (pendingDeleteCommentId === commentKey) {{
              pendingDeleteCommentId = '';
            }}
            queueCommentRender();
          }})
          .catch(function(err) {{
            delete deletingCommentIds[commentKey];
            deleteErrors[commentKey] = err && err.message ? String(err.message) : 'Unable to delete comment.';
            pendingDeleteCommentId = commentKey;
            queueCommentRender();
            throw err;
          }});
      }}

      function saveInlineCommentDraft() {{
        if (!draftComment || draftComment.saving) return;
        var commentText = String(draftComment.text || '').trim();
        if (!commentText) {{
          draftComment.error = 'Comment text is required.';
          draftComment.needsFocus = true;
          queueCommentRender();
          return;
        }}

        var pending = draftComment;
        pending.error = '';
        pending.saving = true;
        queueCommentRender();

        submitComment(
          pending.selection,
          commentText,
          currentCommenterName()
        )
          .then(function() {{
            if (draftComment === pending) {{
              draftComment = null;
            }}
            queueCommentRender();
          }})
          .catch(function(err) {{
            if (draftComment !== pending) return;
            draftComment.saving = false;
            draftComment.error = err && err.message ? String(err.message) : 'Unable to save comment.';
            draftComment.needsFocus = true;
            queueCommentRender();
          }});
      }}

      function isCommentSaveShortcut(event) {{
        if (!event) return false;
        var key = String(event.key || '').toLowerCase();
        var keyCode = Number(event.keyCode || event.which || 0);
        if (key) {{
          if (key !== 'enter' && key !== 'return') return false;
        }} else if (keyCode) {{
          if (keyCode !== 13) return false;
        }} else {{
          return false;
        }}
        if (event.altKey) return false;
        return !!(event.metaKey || event.ctrlKey);
      }}

      function refreshSelectionAction() {{
        if (!previewId) return;
        var selection = getSelectionPayload();
        if (!selection) {{
          hideCommentTrigger();
          return;
        }}
        activeSelection = selection;
        placeCommentTrigger(selection.rect);
      }}

      if (dateEl) {{
        dateEl.textContent = formatDateLabel(payload.date || '');
      }}
      if (bodyEl) {{
        var bodyHtml = payload.body
          ? renderMarkdown(payload.body)
          : '<p class="blog-editor-preview-empty">No content yet.</p>';
        bodyEl.innerHTML = bodyHtml;
      }}

      deleteTokens = loadDeleteTokens();
      if (commenterNameEl) {{
        commenterNameEl.value = loadCommenterName();
        commenterNameEl.addEventListener('input', function() {{
          saveCommenterName(collapseWhitespace(commenterNameEl.value || ''));
          if (draftComment) {{
            queueCommentRender();
          }}
        }});
      }}

      fetchComments();

      if (bodyEl) {{
        bodyEl.addEventListener('mouseup', function() {{
          window.setTimeout(refreshSelectionAction, 0);
        }});
        bodyEl.addEventListener('keyup', function() {{
          window.setTimeout(refreshSelectionAction, 0);
        }});
      }}
      if (commentTriggerEl) {{
        commentTriggerEl.addEventListener('mousedown', function(event) {{
          event.preventDefault();
        }});
        commentTriggerEl.addEventListener('click', function() {{
          startInlineCommentDraft();
        }});
      }}
      if (commentsLayerEl) {{
        commentsLayerEl.addEventListener('input', function(event) {{
          var inputEl = event.target && event.target.closest
            ? event.target.closest('[data-compose-input]')
            : null;
          if (!inputEl || !draftComment) return;
          draftComment.text = String(inputEl.value || '');
        }});
        commentsLayerEl.addEventListener('keydown', function(event) {{
          var inputEl = event.target && event.target.closest
            ? event.target.closest('[data-compose-input]')
            : null;
          if (!inputEl) return;
          if (!isCommentSaveShortcut(event)) return;
          event.preventDefault();
          event.stopPropagation();
          saveInlineCommentDraft();
        }});
        commentsLayerEl.addEventListener('click', function(event) {{
          var target = event.target && event.target.closest
            ? event.target.closest('[data-comment-save], [data-comment-cancel], [data-delete-comment], [data-delete-confirm], [data-delete-cancel]')
            : null;
          if (!target) return;

          if (target.hasAttribute('data-comment-save')) {{
            event.preventDefault();
            saveInlineCommentDraft();
            return;
          }}
          if (target.hasAttribute('data-comment-cancel')) {{
            event.preventDefault();
            cancelInlineCommentDraft();
            return;
          }}
          if (target.hasAttribute('data-delete-comment')) {{
            var deleteId = String(target.getAttribute('data-delete-comment') || '');
            if (!deleteId) return;
            event.preventDefault();
            pendingDeleteCommentId = deleteId;
            deleteErrors[deleteId] = '';
            queueCommentRender();
            return;
          }}
          if (target.hasAttribute('data-delete-cancel')) {{
            var cancelId = String(target.getAttribute('data-delete-cancel') || '');
            event.preventDefault();
            if (cancelId && pendingDeleteCommentId === cancelId) {{
              pendingDeleteCommentId = '';
            }}
            if (cancelId) {{
              delete deleteErrors[cancelId];
            }}
            queueCommentRender();
            return;
          }}
          if (target.hasAttribute('data-delete-confirm')) {{
            var confirmId = String(target.getAttribute('data-delete-confirm') || '');
            if (!confirmId) return;
            event.preventDefault();
            deleteComment(confirmId).catch(function() {{
              // Error is rendered inline in the card.
            }});
            return;
          }}
        }});
      }}

      document.addEventListener('scroll', function() {{
        queueCommentRender();
      }}, {{ passive: true }});
      window.addEventListener('resize', queueCommentRender);
      document.addEventListener('selectionchange', function() {{
        var sel = window.getSelection && window.getSelection();
        if (!sel || sel.rangeCount < 1 || sel.isCollapsed) {{
          hideCommentTrigger();
        }}
      }});

      if (document.fonts && document.fonts.ready && typeof document.fonts.ready.then === 'function') {{
        document.fonts.ready.then(queueCommentRender).catch(function() {{}});
      }}
      if (window.MathJax && window.MathJax.startup && window.MathJax.startup.promise) {{
        window.MathJax.startup.promise.then(function() {{
          queueCommentRender();
        }}).catch(function() {{}});
      }}
      window.setTimeout(queueCommentRender, 180);
    }})();
  </script>
  <script>
    window.MathJax = {{
      tex: {{
        inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
        displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']],
        processEscapes: true
      }},
      options: {{
        skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
      }}
    }};
  </script>
  <script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
</body>
</html>
"""

    def _render_preview_not_found_page(self) -> str:
        site_base = self.server.preview_site_base or "https://ypatel.io"
        site_base = site_base.rstrip("/")
        return f"""<!DOCTYPE html>
<html lang="en-US">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Preview not found</title>
  <link rel="stylesheet" href="{site_base}/assets/css/style.css">
  <link rel="stylesheet" href="{site_base}/static/css/custom.css">
</head>
<body class="blog-standalone">
  <div class="wrapper">
    <section>
      <article class="post-article">
        <h2 class="post-title">Preview Not Available</h2>
        <p class="post-content">This preview link is invalid or has expired.</p>
      </article>
    </section>
  </div>
</body>
</html>
"""

    def _draft_autosave_path(self) -> tuple[str, int | None] | None:
        parsed = urllib.parse.urlparse(self.path)
        prefix = "/api/drafts/"
        if not parsed.path.startswith(prefix):
            return None

        remainder = urllib.parse.unquote(parsed.path[len(prefix) :].strip("/"))
        if not remainder:
            return None

        parts = [part.strip() for part in remainder.split("/") if part.strip()]
        if len(parts) == 2 and parts[1] == "autosaves":
            if "/" in parts[0]:
                return None
            return parts[0], None
        if len(parts) == 3 and parts[1] == "autosaves":
            if "/" in parts[0]:
                return None
            if not parts[2].isdigit():
                return None
            return parts[0], int(parts[2])
        return None

    def do_OPTIONS(self) -> None:
        origin = self.headers.get("Origin")
        self.send_response(204)
        self._set_cors_headers(origin)
        self.end_headers()

    def do_GET(self) -> None:
        origin = self.headers.get("Origin")
        parsed = urllib.parse.urlparse(self.path)

        preview_id = self._preview_id_from_path()
        if preview_id is not None:
            preview = self.server.store.get_shared_preview(preview_id)
            if preview is None:
                self._send_html(404, self._render_preview_not_found_page(), origin)
                return
            self._send_html(200, self._render_shared_preview_page(preview), origin)
            return

        preview_comments_id = self._preview_comments_id_from_path()
        if preview_comments_id is not None:
            preview = self.server.store.get_shared_preview(preview_comments_id)
            if preview is None:
                self._send_json(404, {"error": "Preview not found"}, origin)
                return
            comments = self.server.store.list_shared_preview_comments(preview_comments_id)
            self._send_json(200, {"comments": comments}, origin)
            return

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

        autosave_route = self._draft_autosave_path()
        if autosave_route is not None:
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return

            draft_id, autosave_id = autosave_route
            if autosave_id is None:
                query = urllib.parse.parse_qs(parsed.query or "")
                raw_limit = (query.get("limit") or ["100"])[0]
                try:
                    limit = max(1, min(500, int(raw_limit)))
                except Exception:  # noqa: BLE001
                    limit = 100
                autosaves = self.server.store.list_autosaves(draft_id, limit=limit)
                self._send_json(200, {"autosaves": autosaves}, origin)
                return

            autosave = self.server.store.get_autosave(draft_id, autosave_id)
            if autosave is None:
                self._send_json(404, {"error": "Autosave not found"}, origin)
                return
            self._send_json(200, {"autosave": autosave}, origin)
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
        autosave_route = self._draft_autosave_path()
        preview_comments_id = self._preview_comments_id_from_path()

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

        if preview_comments_id is not None:
            try:
                payload = self._read_json()
            except Exception as exc:  # noqa: BLE001
                self._send_json(400, {"error": f"Invalid JSON payload: {exc}"}, origin)
                return
            try:
                comment = self.server.store.create_shared_preview_comment(
                    preview_comments_id,
                    payload,
                )
                delete_token = str(comment.pop("delete_token", "")).strip()
                self._send_json(
                    200,
                    {"comment": comment, "delete_token": delete_token},
                    origin,
                )
            except KeyError:
                self._send_json(404, {"error": "Preview not found"}, origin)
            except ValueError as exc:
                self._send_json(400, {"error": str(exc)}, origin)
            except RuntimeError as exc:
                self._send_json(429, {"error": str(exc)}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(500, {"error": str(exc)}, origin)
            return

        if autosave_route is not None:
            draft_id, autosave_id = autosave_route
            if autosave_id is not None:
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

            try:
                autosave = self.server.store.create_autosave(draft_id, payload)
                self._send_json(200, {"autosave": autosave}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(500, {"error": str(exc)}, origin)
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

        if parsed.path == "/api/previews":
            if not self._authorized():
                self._send_json(401, {"error": "Unauthorized"}, origin)
                return
            try:
                payload = self._read_json()
            except Exception as exc:  # noqa: BLE001
                self._send_json(400, {"error": f"Invalid JSON payload: {exc}"}, origin)
                return
            try:
                preview = self.server.store.create_shared_preview(
                    payload,
                    ttl_seconds=self.server.preview_ttl_seconds,
                )
                preview_url = (
                    self._resolved_preview_base_url()
                    + "/preview/"
                    + urllib.parse.quote(str(preview.get("preview_id", "")))
                )
                self._send_json(200, {"preview": preview, "preview_url": preview_url}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(500, {"error": str(exc)}, origin)
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

    def do_DELETE(self) -> None:
        origin = self.headers.get("Origin")
        preview_comment_path = self._preview_comment_delete_path()
        if preview_comment_path is not None:
            preview_id, comment_id = preview_comment_path
            delete_token = str(self.headers.get("X-Comment-Delete-Token", "")).strip()
            if not delete_token:
                parsed = urllib.parse.urlparse(self.path)
                query = urllib.parse.parse_qs(parsed.query or "")
                delete_token = str((query.get("token") or [""])[0]).strip()
            if not delete_token:
                self._send_json(400, {"error": "Delete token is required."}, origin)
                return
            try:
                deleted = self.server.store.delete_shared_preview_comment(
                    preview_id,
                    comment_id,
                    delete_token,
                )
                if not deleted:
                    self._send_json(404, {"error": "Comment not found"}, origin)
                    return
                self._send_json(
                    200,
                    {"ok": True, "preview_id": preview_id, "comment_id": comment_id},
                    origin,
                )
            except KeyError as exc:
                message = str(exc).strip("'")
                if message == "Comment not found":
                    self._send_json(404, {"error": "Comment not found"}, origin)
                else:
                    self._send_json(404, {"error": "Preview not found"}, origin)
            except PermissionError:
                self._send_json(403, {"error": "Invalid delete token."}, origin)
            except ValueError as exc:
                self._send_json(400, {"error": str(exc)}, origin)
            except Exception as exc:  # noqa: BLE001
                self._send_json(500, {"error": str(exc)}, origin)
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
                deleted_remote = self.server.publisher.delete_post(filename)
                deleted_cached = self.server.store.delete_cached_published_post(filename)
                if not deleted_remote and not deleted_cached:
                    self._send_json(404, {"error": "Post not found"}, origin)
                    return
                self._send_json(
                    200,
                    {"ok": True, "filename": filename, "deleted_remote": deleted_remote},
                    origin,
                )
            except Exception as exc:  # noqa: BLE001
                self._send_json(502, {"error": str(exc)}, origin)
            return

        draft_id = self._draft_id_from_path()
        if draft_id is None:
            self._send_json(404, {"error": "Not found"}, origin)
            return
        if not self._authorized():
            self._send_json(401, {"error": "Unauthorized"}, origin)
            return

        deleted = self.server.store.delete_draft(draft_id)
        if not deleted:
            self._send_json(404, {"error": "Draft not found"}, origin)
            return
        self._send_json(200, {"ok": True, "draft_id": draft_id}, origin)


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
    preview_base_url = os.getenv("DRAFT_DB_PREVIEW_BASE_URL", "").strip()
    preview_site_base = os.getenv("DRAFT_DB_PREVIEW_SITE_BASE", "https://ypatel.io").strip() or "https://ypatel.io"
    preview_ttl_seconds = int(
        os.getenv("DRAFT_DB_PREVIEW_TTL_SECONDS", str(DEFAULT_PREVIEW_TTL_SECONDS))
    )
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
        preview_base_url,
        preview_site_base,
        preview_ttl_seconds,
    )
    print(
        f"Draft API listening on http://{args.host}:{args.port} "
        f"(db={db_path}, origins={sorted(allowed_origins)}, session_auth={auth_manager.supports_session}, "
        f"github_publish={publisher.configured}, github_repo={publisher.repo}, github_branch={publisher.branch}, "
        f"preview_base_url={preview_base_url or 'auto'}, preview_ttl_seconds={preview_ttl_seconds})"
    )
    server.serve_forever()


if __name__ == "__main__":
    main()
