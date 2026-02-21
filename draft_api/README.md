# Draft API

SQLite-backed authenticated API for editor drafts.

`/make-post/` can use this API in two modes:

1. `token` mode: static bearer token (`DRAFT_DB_TOKEN`).
2. `session` mode (recommended): passphrase login at `POST /api/session`, which returns a short-lived bearer token.

No auth secret is stored in this repo.

## Local Run (session mode, recommended)

```bash
cd /Users/yash/Documents/Personal/yashpatel5400.github.io
export DRAFT_DB_OWNER_PASSPHRASE='your-strong-passphrase'
export DRAFT_DB_SESSION_SECRET='long-random-secret-at-least-32-bytes'
python3 draft_api/server.py
```

## Local Run (legacy static token mode)

```bash
cd /Users/yash/Documents/Personal/yashpatel5400.github.io
export DRAFT_DB_TOKEN='replace-with-a-long-random-token'
python3 draft_api/server.py
```

## Editor Config

In `/Users/yash/Documents/Personal/yashpatel5400.github.io/_data/editor.yml`:

```yaml
draft_api_base: "http://127.0.0.1:8787"
draft_api_auth_mode: "session" # or "token"
draft_id: "main"
```

## Environment Variables

- `DRAFT_DB_HOST` (default: `127.0.0.1`)
- `DRAFT_DB_PORT` (default: `8787`, falls back to `PORT` if set)
- `DRAFT_DB_PATH` (default: `draft_api/drafts.sqlite3`)
- `DRAFT_DB_ALLOWED_ORIGINS` (comma-separated CORS allowlist)
- `DRAFT_DB_SESSION_TTL_SECONDS` (default: `28800`, 8 hours)
- `DRAFT_DB_LOGIN_WINDOW_SECONDS` (default: `300`)
- `DRAFT_DB_LOGIN_MAX_ATTEMPTS` (default: `10`)

Auth variables:

- Session mode: `DRAFT_DB_OWNER_PASSPHRASE` + `DRAFT_DB_SESSION_SECRET`
- Token mode: `DRAFT_DB_TOKEN`

## Deploying Remotely

Any host that can run Python works (Fly.io, Railway, Render, VPS, etc.).

Requirements:

1. Persist the SQLite file by mounting a volume.
2. Set `DRAFT_DB_ALLOWED_ORIGINS` to your site origin(s), for example:
   - `https://ypatel.io,https://yashpatel5400.github.io`
3. Set secrets as host environment variables (never in git).
4. Update `draft_api_base` in `/Users/yash/Documents/Personal/yashpatel5400.github.io/_data/editor.yml` to your deployed API URL.

## API

- `GET /health` (no auth)
- `POST /api/session` (session mode only)
- `GET /api/drafts/<draft_id>` (Bearer token)
- `PUT /api/drafts/<draft_id>` (Bearer token)

`PUT` payload fields:

- `title`
- `date`
- `body`
- `filename`
- `markdown`
