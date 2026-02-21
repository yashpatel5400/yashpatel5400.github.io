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

    if (!expectedKeyHex || !pbkdf2SaltHex || !pbkdf2Iterations) return;

    const statusEl = shell.querySelector('[data-editor-status]');
    const lockBtn = shell.querySelector('[data-editor-lock-btn]');
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

    let shellVisible = false;
    let failedAttempts = 0;
    let blockedUntil = 0;

    function setStatus(message, kind) {
      if (!statusEl) return;
      statusEl.textContent = message;
      statusEl.classList.remove('is-error', 'is-success');
      if (kind) statusEl.classList.add(kind === 'error' ? 'is-error' : 'is-success');
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

    function saveDraft(showMessage) {
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

    function loadDraft(showMessage) {
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

    function scheduleAutosave() {
      if (autosaveTimer) window.clearTimeout(autosaveTimer);
      autosaveTimer = window.setTimeout(function() {
        saveDraft(false);
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

    function showShell() {
      shell.hidden = false;
      if (lockState) lockState.hidden = true;
      shellVisible = true;
      loadDraft(false);
      if (!dateInput.value) dateInput.value = todayString();
      updatePreview();
      refreshPreviewWhenRenderersReady();
      titleInput.focus();
    }

    function hideShell() {
      saveDraft(false);
      shell.hidden = true;
      if (lockState) lockState.hidden = false;
      shellVisible = false;
      setStatus('', null);
    }

    async function requestUnlockAndShow() {
      if (shellVisible) return;

      const now = Date.now();
      if (now < blockedUntil) {
        window.alert('Editor temporarily blocked. Try again in a minute.');
        return;
      }

      const passphrase = window.prompt('Passphrase');
      if (passphrase === null || !passphrase.trim()) return;

      try {
        const derivedHex = await derivePassphraseKeyHex(passphrase.trim());
        if (derivedHex !== expectedKeyHex) {
          failedAttempts += 1;
          if (failedAttempts >= 5) {
            failedAttempts = 0;
            blockedUntil = Date.now() + 60000;
          }
          window.alert('Unable to open editor.');
          return;
        }

        failedAttempts = 0;
        showShell();
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

    if (saveBtn) {
      saveBtn.addEventListener('click', function() {
        saveDraft(true);
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
      if (shellVisible) saveDraft(false);
    });

    hideShell();
    maybeRevealFromHash();
  })();
</script>
{% endif %}
