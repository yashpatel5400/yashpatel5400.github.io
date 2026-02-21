---
layout: default
title: Make Post
permalink: /make-post/
sitemap: false
---

<p align="center">
  <a href="{{ '/' | relative_url }}">Home</a> |
  <a href="{{ '/' | relative_url }}#papers">Selected Papers</a> |
  <a href="{{ '/' | relative_url }}#mentoring">Mentoring</a> |
  <a href="{{ '/' | relative_url }}#projects">Projects</a> |
  <a href="{{ '/blog/' | relative_url }}">Blog</a>
</p>

{% if site.blog_editor_enabled %}
<article class="make-post-page">
  <section class="make-post-lock" data-editor-lock-state>
    <button type="button" data-editor-unlock>Unlock</button>
  </section>

  <section
    class="blog-editor make-post-editor"
    id="blog-owner-editor"
    data-editor-repo="{{ site.blog_editor_repo }}"
    data-editor-branch="{{ site.blog_editor_branch }}"
    data-draft-api-base="{{ site.data.editor.draft_api_base }}"
    data-draft-api-auth="{{ site.data.editor.draft_api_auth_mode | default: 'session' }}"
    data-draft-id="{{ site.data.editor.draft_id | default: 'main' }}"
    hidden
  >
    <div class="blog-editor-workbench">
      <div class="blog-editor-compose">
        <div class="blog-editor-meta-row">
          <div class="blog-editor-meta-field blog-editor-meta-field--title">
            <label for="blog-editor-title">Title</label>
            <input type="text" id="blog-editor-title" placeholder="Post title" />
          </div>
          <div class="blog-editor-meta-field blog-editor-meta-field--date">
            <label for="blog-editor-date">Date</label>
            <input type="date" id="blog-editor-date" />
          </div>
        </div>

        <label for="blog-editor-body">Markdown / LaTeX</label>
        <textarea
          id="blog-editor-body"
          class="blog-editor-body-input"
          rows="20"
          placeholder="Write markdown and equations like $\\alpha$ or $$\\int_0^1 x^2 dx$$..."
        ></textarea>

        <div class="blog-editor-output">
          <span>Output file:</span>
          <code data-editor-filename>YYYY-MM-DD-my-post.md</code>
        </div>

        <div class="blog-editor-actions">
          <button type="button" data-editor-connect-db>Reconnect</button>
          <button type="button" data-editor-save>Save Draft</button>
          <button type="button" data-editor-copy>Copy Markdown</button>
          <button type="button" data-editor-download>Download File</button>
          <button type="button" data-editor-open-github>Open GitHub Prefill</button>
          <button type="button" data-editor-lock-btn>Lock</button>
        </div>
        <p class="blog-editor-status" data-editor-status aria-live="polite"></p>
      </div>

      <div class="blog-editor-render">
        <h4>Rendered Preview</h4>
        <div class="blog-editor-preview" data-editor-preview></div>
      </div>
    </div>
  </section>
</article>

<script>
  window.MathJax = {
    tex: {
      inlineMath: [['$', '$'], ['\\(', '\\)']],
      displayMath: [['$$', '$$'], ['\\[', '\\]']],
      processEscapes: true
    },
    options: {
      skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
    }
  };
</script>
<script defer src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/dompurify@3.1.6/dist/purify.min.js"></script>
<script defer id="MathJax-script" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
<script>
  (function() {
    const shell = document.getElementById('blog-owner-editor');
    if (!shell || shell.dataset.editorReady === '1') return;
    shell.dataset.editorReady = '1';

    const lockState = document.querySelector('[data-editor-lock-state]');
    const unlockBtn = document.querySelector('[data-editor-unlock]');
    const expectedKeyHex = '{{ site.data.editor.guard }}'.trim().toLowerCase();
    const pbkdf2SaltHex = '{{ site.data.editor.grain }}'.trim().toLowerCase();
    const pbkdf2Iterations = Number('{{ site.data.editor.rounds }}') || 310000;
    const repo = shell.dataset.editorRepo || '';
    const branch = shell.dataset.editorBranch || 'master';
    const draftApiBase = (shell.dataset.draftApiBase || '').trim().replace(/\/+$/, '');
    const draftApiAuthMode = (shell.dataset.draftApiAuth || 'session').trim().toLowerCase();
    const draftId = (shell.dataset.draftId || 'main').trim();
    const sessionUnlockEnabled = draftApiAuthMode === 'session' && Boolean(draftApiBase);
    const localUnlockEnabled = Boolean(expectedKeyHex && pbkdf2SaltHex && pbkdf2Iterations) && !sessionUnlockEnabled;

    const statusEl = shell.querySelector('[data-editor-status]');
    const lockBtn = shell.querySelector('[data-editor-lock-btn]');
    const connectDbBtn = shell.querySelector('[data-editor-connect-db]');
    const titleInput = shell.querySelector('#blog-editor-title');
    const dateInput = shell.querySelector('#blog-editor-date');
    const bodyInput = shell.querySelector('#blog-editor-body');
    const previewEl = shell.querySelector('[data-editor-preview]');
    const filenameEl = shell.querySelector('[data-editor-filename]');
    const saveBtn = shell.querySelector('[data-editor-save]');
    const copyBtn = shell.querySelector('[data-editor-copy]');
    const downloadBtn = shell.querySelector('[data-editor-download]');
    const openGithubBtn = shell.querySelector('[data-editor-open-github]');
    const draftStorageKey = 'make-post-draft-v1';
    const draftApiTokenStorageKey = 'make-post-draft-api-token-v1';
    const draftApiTokenPersistentStorageKey = 'make-post-draft-api-token-persist-v1';

    let shellVisible = false;
    let failedAttempts = 0;
    let blockedUntil = 0;

    function setStatus(message, kind) {
      if (!statusEl) return;
      statusEl.textContent = message;
      statusEl.classList.remove('is-error', 'is-success');
      if (kind) statusEl.classList.add(kind === 'error' ? 'is-error' : 'is-success');
    }

    function hasDraftApiConfigured() {
      return Boolean(draftApiBase);
    }

    function isSessionAuthMode() {
      return draftApiAuthMode === 'session';
    }

    function getStoredApiToken() {
      try {
        const sessionToken = window.sessionStorage.getItem(draftApiTokenStorageKey);
        if (sessionToken) return sessionToken;
        const persistedToken = window.localStorage.getItem(draftApiTokenPersistentStorageKey) || '';
        if (persistedToken) {
          window.sessionStorage.setItem(draftApiTokenStorageKey, persistedToken);
          return persistedToken;
        }
        return '';
      } catch (err) {
        return '';
      }
    }

    function setStoredApiToken(token) {
      try {
        if (token) {
          window.sessionStorage.setItem(draftApiTokenStorageKey, token);
          window.localStorage.setItem(draftApiTokenPersistentStorageKey, token);
        } else {
          window.sessionStorage.removeItem(draftApiTokenStorageKey);
          window.localStorage.removeItem(draftApiTokenPersistentStorageKey);
        }
      } catch (err) {
        // no-op
      }
    }

    async function requestSessionToken(passphrase) {
      const response = await fetch(draftApiBase + '/api/session', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ passphrase: passphrase })
      });
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      const token = payload && typeof payload.token === 'string' ? payload.token.trim() : '';
      if (!token) {
        throw new Error('Draft DB session response is invalid.');
      }
      setStoredApiToken(token);
      return token;
    }

    async function ensureApiToken(forcePrompt, passphraseHint) {
      if (!hasDraftApiConfigured()) return '';
      if (!forcePrompt) {
        const existing = getStoredApiToken();
        if (existing) return existing;
      }

      if (isSessionAuthMode()) {
        const passphraseInput =
          typeof passphraseHint === 'string' && passphraseHint.trim()
            ? passphraseHint.trim()
            : window.prompt('Passphrase');
        if (!passphraseInput || !passphraseInput.trim()) return '';
        const token = await requestSessionToken(passphraseInput.trim());
        setStoredApiToken(token);
        return token;
      }

      const tokenInput = window.prompt('Draft DB token');
      if (!tokenInput || !tokenInput.trim()) return '';
      const token = tokenInput.trim();
      setStoredApiToken(token);
      return token;
    }

    function todayString() {
      const now = new Date();
      const month = String(now.getMonth() + 1).padStart(2, '0');
      const day = String(now.getDate()).padStart(2, '0');
      return now.getFullYear() + '-' + month + '-' + day;
    }

    function slugify(text) {
      const normalized = (text || '')
        .toLowerCase()
        .trim()
        .replace(/['"]/g, '')
        .replace(/[^a-z0-9]+/g, '-')
        .replace(/^-+|-+$/g, '');
      return normalized || 'new-post';
    }

    function yamlEscape(text) {
      return String(text || '').replace(/\\/g, '\\\\').replace(/"/g, '\\"');
    }

    function ensureDate() {
      if (!dateInput.value) dateInput.value = todayString();
      return dateInput.value;
    }

    function escapeHtml(text) {
      return String(text || '')
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
    }

    function formatDateLabel(dateString) {
      if (!dateString) return '';
      const parsed = new Date(dateString + 'T00:00:00');
      if (Number.isNaN(parsed.getTime())) return dateString;
      return parsed.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'long',
        day: 'numeric'
      });
    }

    function renderMarkdownToHtml(markdown) {
      const raw = String(markdown || '');
      if (window.marked && typeof window.marked.parse === 'function') {
        const parsed = window.marked.parse(raw, {
          gfm: true,
          breaks: true,
          mangle: false,
          headerIds: true
        });
        if (window.DOMPurify && typeof window.DOMPurify.sanitize === 'function') {
          return window.DOMPurify.sanitize(parsed, { USE_PROFILES: { html: true } });
        }
        return parsed;
      }
      return '<pre>' + escapeHtml(raw) + '</pre>';
    }

    function renderMathInPreview() {
      if (!window.MathJax || typeof window.MathJax.typesetPromise !== 'function') return;
      if (typeof window.MathJax.typesetClear === 'function') {
        window.MathJax.typesetClear([previewEl]);
      }
      window.MathJax.typesetPromise([previewEl]).catch(function() {
        // no-op
      });
    }

    function buildPostContent(allowPartial) {
      const title = titleInput.value.trim();
      const date = ensureDate();
      const slug = slugify(title);
      const body = bodyInput.value.trim();

      if (!allowPartial && !title) throw new Error('Title is required.');
      if (!allowPartial && !body) throw new Error('Markdown body is required.');

      const effectiveTitle = title || 'Untitled Draft';
      const filename = date + '-' + slug + '.md';
      const frontMatter = [
        '---',
        'layout: post',
        'title: "' + yamlEscape(effectiveTitle) + '"',
        'date: ' + date,
        '---',
        ''
      ];

      return {
        filename: filename,
        title: effectiveTitle,
        date: date,
        body: body,
        markdown: frontMatter.join('\n') + body + '\n'
      };
    }

    let previewTimer = null;
    let autosaveTimer = null;
    function schedulePreview() {
      if (previewTimer) window.clearTimeout(previewTimer);
      previewTimer = window.setTimeout(updatePreview, 120);
    }

    function saveDraftLocal(showMessage) {
      try {
        const payload = {
          title: titleInput.value,
          date: dateInput.value,
          body: bodyInput.value,
          savedAt: new Date().toISOString()
        };
        window.localStorage.setItem(draftStorageKey, JSON.stringify(payload));
        if (showMessage) setStatus('Draft saved locally.', 'success');
        return true;
      } catch (err) {
        if (showMessage) {
          setStatus('Unable to save draft in this browser.', 'error');
        }
        return false;
      }
    }

    function loadDraftLocal(showMessage) {
      try {
        const raw = window.localStorage.getItem(draftStorageKey);
        if (!raw) return false;
        const payload = JSON.parse(raw);
        if (!payload || typeof payload !== 'object') return false;
        if (typeof payload.title === 'string') titleInput.value = payload.title;
        if (typeof payload.date === 'string') dateInput.value = payload.date;
        if (typeof payload.body === 'string') bodyInput.value = payload.body;
        if (!dateInput.value) dateInput.value = todayString();
        if (showMessage) setStatus('Draft restored from local save.', 'success');
        return true;
      } catch (err) {
        if (showMessage) {
          setStatus('Saved draft could not be restored.', 'error');
        }
        return false;
      }
    }

    async function parseErrorMessage(response) {
      try {
        const payload = await response.json();
        if (payload && typeof payload.error === 'string') return payload.error;
      } catch (err) {
        // no-op
      }
      return 'Draft DB request failed.';
    }

    async function apiRequest(path, options, promptForToken) {
      if (!hasDraftApiConfigured()) return null;
      let token = getStoredApiToken();
      if (!token && promptForToken) {
        token = await ensureApiToken(true);
      }
      if (!token) return null;

      const request = Object.assign({}, options || {});
      const headers = Object.assign({}, request.headers || {});
      headers.Authorization = 'Bearer ' + token;
      if (!headers['Content-Type'] && request.body) {
        headers['Content-Type'] = 'application/json';
      }
      request.headers = headers;

      let response = await fetch(draftApiBase + path, request);
      if (response.status === 401 && promptForToken) {
        setStoredApiToken('');
        token = await ensureApiToken(true);
        if (!token) return null;
        request.headers.Authorization = 'Bearer ' + token;
        response = await fetch(draftApiBase + path, request);
      }
      return response;
    }

    async function loadDraftRemote(showMessage, promptForToken) {
      if (!hasDraftApiConfigured()) return false;
      const response = await apiRequest('/api/drafts/' + encodeURIComponent(draftId), { method: 'GET' }, promptForToken);
      if (response === null) return false;
      if (response.status === 404) {
        if (showMessage) setStatus('Connected to Draft DB. No remote draft yet.', 'success');
        return false;
      }
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      const payload = await response.json();
      const draft = payload && payload.draft ? payload.draft : null;
      if (!draft || typeof draft !== 'object') return false;

      if (typeof draft.title === 'string') titleInput.value = draft.title;
      if (typeof draft.draft_date === 'string') dateInput.value = draft.draft_date;
      if (typeof draft.body === 'string') bodyInput.value = draft.body;
      if (!dateInput.value) dateInput.value = todayString();
      saveDraftLocal(false);
      if (showMessage) setStatus('Draft loaded from database.', 'success');
      return true;
    }

    async function saveDraftRemote(showMessage, promptForToken) {
      if (!hasDraftApiConfigured()) return false;
      const built = buildPostContent(true);
      const payload = {
        title: titleInput.value,
        date: ensureDate(),
        body: bodyInput.value,
        filename: built.filename,
        markdown: built.markdown
      };
      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(draftId),
        { method: 'PUT', body: JSON.stringify(payload) },
        promptForToken
      );
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      if (showMessage) setStatus('Draft saved to database.', 'success');
      return true;
    }

    function scheduleAutosave() {
      if (autosaveTimer) window.clearTimeout(autosaveTimer);
      autosaveTimer = window.setTimeout(function() {
        saveDraftLocal(false);
      }, 400);
    }

    function onEditorInput() {
      schedulePreview();
      scheduleAutosave();
    }

    function refreshPreviewWhenRenderersReady() {
      let attempts = 0;
      const intervalId = window.setInterval(function() {
        attempts += 1;
        const markdownReady = !!(window.marked && typeof window.marked.parse === 'function');
        const sanitizeReady = !!(window.DOMPurify && typeof window.DOMPurify.sanitize === 'function');
        const mathReady = !!(window.MathJax && typeof window.MathJax.typesetPromise === 'function');
        if ((markdownReady && sanitizeReady && mathReady) || attempts > 20) {
          window.clearInterval(intervalId);
          schedulePreview();
        }
      }, 250);
    }

    function updatePreview() {
      try {
        const built = buildPostContent(true);
        const renderedBody = built.body
          ? renderMarkdownToHtml(built.body)
          : '<p class="blog-editor-preview-empty">Start writing markdown on the left.</p>';
        const dateLabel = formatDateLabel(built.date);

        filenameEl.textContent = built.filename;
        previewEl.innerHTML =
          '<article class="blog-editor-preview-article">' +
            '<h1 class="blog-editor-preview-title">' + escapeHtml(built.title) + '</h1>' +
            (dateLabel ? '<p class="blog-editor-preview-date">' + escapeHtml(dateLabel) + '</p>' : '') +
            '<div class="post-content blog-editor-preview-content">' + renderedBody + '</div>' +
          '</article>';

        renderMathInPreview();
        setStatus('', null);
      } catch (err) {
        filenameEl.textContent = 'YYYY-MM-DD-my-post.md';
        previewEl.innerHTML = '<p class="blog-editor-preview-empty">Unable to render preview.</p>';
        if (err && err.message) setStatus(err.message, 'error');
      }
    }

    function hexToBytes(hex) {
      if (!hex || hex.length % 2 !== 0) throw new Error('Invalid KDF salt.');
      const bytes = new Uint8Array(hex.length / 2);
      for (let i = 0; i < bytes.length; i += 1) {
        bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
      }
      return bytes;
    }

    function bytesToHex(bytes) {
      return Array.from(bytes).map(function(byte) {
        return byte.toString(16).padStart(2, '0');
      }).join('');
    }

    async function derivePassphraseKeyHex(passphrase) {
      if (!window.crypto || !window.crypto.subtle) {
        throw new Error('Browser crypto API not available.');
      }
      const keyMaterial = await window.crypto.subtle.importKey(
        'raw',
        new TextEncoder().encode(passphrase),
        { name: 'PBKDF2' },
        false,
        ['deriveBits']
      );
      const bits = await window.crypto.subtle.deriveBits(
        {
          name: 'PBKDF2',
          salt: hexToBytes(pbkdf2SaltHex),
          iterations: pbkdf2Iterations,
          hash: 'SHA-256'
        },
        keyMaterial,
        256
      );
      return bytesToHex(new Uint8Array(bits));
    }

    async function showShell() {
      shell.hidden = false;
      if (lockState) lockState.hidden = true;
      shellVisible = true;
      loadDraftLocal(false);
      if (hasDraftApiConfigured() && getStoredApiToken()) {
        try {
          await loadDraftRemote(false, false);
        } catch (err) {
          // no-op
        }
      }
      if (!dateInput.value) dateInput.value = todayString();
      updatePreview();
      refreshPreviewWhenRenderersReady();
      titleInput.focus();
    }

    function hideShell() {
      saveDraftLocal(false);
      shell.hidden = true;
      if (lockState) lockState.hidden = false;
      shellVisible = false;
      setStatus('', null);
    }

    async function requestUnlockAndShow() {
      if (shellVisible) return;

      const hasSessionUnlock = hasDraftApiConfigured() && isSessionAuthMode();
      if (!localUnlockEnabled && !hasSessionUnlock) {
        window.alert('Editor authentication is not configured.');
        return;
      }

      const now = Date.now();
      if (now < blockedUntil) {
        window.alert('Editor temporarily blocked. Try again in a minute.');
        return;
      }

      if (hasSessionUnlock) {
        const existingToken = getStoredApiToken();
        if (existingToken) {
          try {
            await loadDraftRemote(false, false);
            failedAttempts = 0;
            await showShell();
            setStatus('Editor unlocked.', 'success');
            return;
          } catch (err) {
            const lower = String(err && err.message ? err.message : '').toLowerCase();
            if (lower.indexOf('unauthorized') !== -1) {
              setStoredApiToken('');
            }
          }
        }
      }

      const passphrase = window.prompt('Passphrase');
      if (passphrase === null || !passphrase.trim()) return;

      try {
        const normalizedPassphrase = passphrase.trim();

        if (localUnlockEnabled) {
          const derivedHex = await derivePassphraseKeyHex(normalizedPassphrase);
          if (derivedHex !== expectedKeyHex) {
            failedAttempts += 1;
            if (failedAttempts >= 5) {
              failedAttempts = 0;
              blockedUntil = Date.now() + 60000;
            }
            window.alert('Unable to open editor.');
            return;
          }
        }

        if (hasSessionUnlock) {
          const token = await ensureApiToken(false, normalizedPassphrase);
          if (!token) {
            failedAttempts += 1;
            if (failedAttempts >= 5) {
              failedAttempts = 0;
              blockedUntil = Date.now() + 60000;
            }
            window.alert('Unable to open editor.');
            return;
          }
        }

        failedAttempts = 0;
        await showShell();
        setStatus('Editor unlocked.', 'success');
      } catch (err) {
        window.alert('Unable to open editor.');
      }
    }

    function maybeRevealFromHash() {
      const hash = (window.location.hash || '').toLowerCase();
      if (hash === '#compose' || hash === '#draft') {
        requestUnlockAndShow();
      }
    }

    function isComposeShortcut(event) {
      const key = (event.key || '').toLowerCase();
      if (key !== 'e' || !event.shiftKey) return false;
      return event.altKey || event.metaKey;
    }

    if (unlockBtn) {
      unlockBtn.addEventListener('click', function() {
        requestUnlockAndShow();
      });
    }

    lockBtn.addEventListener('click', function() {
      hideShell();
    });

    if (connectDbBtn) {
      connectDbBtn.addEventListener('click', async function() {
        if (!hasDraftApiConfigured()) {
          setStatus('Draft DB URL is not configured in _data/editor.yml.', 'error');
          return;
        }
        let token = '';
        try {
          token = await ensureApiToken(true);
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to authenticate with Draft DB.', 'error');
          return;
        }
        if (!token) {
          setStatus(
            isSessionAuthMode()
              ? 'Passphrase is required to connect.'
              : 'Draft DB token is required to connect.',
            'error'
          );
          return;
        }
        try {
          const restored = await loadDraftRemote(false, false);
          updatePreview();
          if (restored) {
            setStatus('Connected to Draft DB and loaded draft.', 'success');
          } else {
            setStatus('Connected to Draft DB.', 'success');
          }
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to connect to Draft DB.', 'error');
        }
      });
    }

    if (saveBtn) {
      saveBtn.addEventListener('click', async function() {
        const localSaved = saveDraftLocal(false);
        if (!hasDraftApiConfigured()) {
          if (localSaved) {
            setStatus('Saved locally. Configure Draft DB URL for backend saves.', 'success');
          } else {
            setStatus('Unable to save draft locally.', 'error');
          }
          return;
        }

        try {
          const remoteSaved = await saveDraftRemote(false, true);
          if (remoteSaved) {
            setStatus('Draft saved to database.', 'success');
            return;
          }
          if (localSaved) {
            setStatus(
              isSessionAuthMode()
                ? 'Saved locally. Passphrase is required for backend save.'
                : 'Saved locally. Draft DB token is required for backend save.',
              'error'
            );
          } else {
            setStatus('Unable to save draft.', 'error');
          }
        } catch (err) {
          if (localSaved) {
            setStatus('Saved locally. Database save failed: ' + (err.message || 'unknown error') + '.', 'error');
          } else {
            setStatus(err && err.message ? err.message : 'Unable to save draft.', 'error');
          }
        }
      });
    }

    titleInput.addEventListener('input', onEditorInput);
    dateInput.addEventListener('input', onEditorInput);
    bodyInput.addEventListener('input', onEditorInput);

    copyBtn.addEventListener('click', async function() {
      try {
        const built = buildPostContent();
        await navigator.clipboard.writeText(built.markdown);
        setStatus('Markdown copied to clipboard.', 'success');
      } catch (err) {
        setStatus(err && err.message ? err.message : 'Unable to copy markdown.', 'error');
      }
    });

    downloadBtn.addEventListener('click', function() {
      try {
        const built = buildPostContent();
        const blob = new Blob([built.markdown], { type: 'text/markdown;charset=utf-8' });
        const link = document.createElement('a');
        link.href = URL.createObjectURL(blob);
        link.download = built.filename;
        document.body.appendChild(link);
        link.click();
        document.body.removeChild(link);
        URL.revokeObjectURL(link.href);
        setStatus('Draft downloaded as ' + built.filename + '.', 'success');
      } catch (err) {
        setStatus(err && err.message ? err.message : 'Unable to download markdown.', 'error');
      }
    });

    openGithubBtn.addEventListener('click', function() {
      try {
        const built = buildPostContent();
        if (!repo) throw new Error('Missing GitHub repository config.');
        const params = new URLSearchParams({
          filename: built.filename,
          value: built.markdown
        });
        const url = 'https://github.com/' + repo + '/new/' + branch + '/_posts?' + params.toString();
        window.open(url, '_blank', 'noopener');
      } catch (err) {
        setStatus(err && err.message ? err.message : 'Unable to open GitHub prefill.', 'error');
      }
    });

    document.addEventListener('keydown', function(event) {
      if (isComposeShortcut(event)) {
        event.preventDefault();
        requestUnlockAndShow();
      }
    });

    window.addEventListener('hashchange', maybeRevealFromHash);
    window.addEventListener('beforeunload', function() {
      if (shellVisible) saveDraftLocal(false);
    });

    hideShell();
    maybeRevealFromHash();
  })();
</script>
{% endif %}
