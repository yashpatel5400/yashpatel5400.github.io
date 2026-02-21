---
layout: default
title: Writing
permalink: /blog/
---

<p align="center">
  <a href="{{ '/' | relative_url }}">Home</a> |
  <a href="{{ '/' | relative_url }}#papers">Selected Papers</a> |
  <a href="{{ '/' | relative_url }}#mentoring">Mentoring</a> |
  <a href="{{ '/' | relative_url }}#projects">Projects</a> |
  <span class="nav-current">Blog</span>
</p>

{% if site.blog_editor_enabled %}
<section
  class="blog-editor"
  id="blog-owner-editor"
  data-editor-repo="{{ site.blog_editor_repo }}"
  data-editor-branch="{{ site.blog_editor_branch }}"
  hidden
>
  <div class="blog-editor-panel" data-editor-panel hidden>
    <div class="blog-editor-header">
      <h3>Draft Console</h3>
      <button type="button" data-editor-lock-btn>Hide</button>
    </div>
    <p class="blog-editor-note">
      This generates a Jekyll post file for <code>_posts/</code>, with preview, copy/download, and GitHub prefill.
    </p>
    <div class="blog-editor-workbench">
      <div class="blog-editor-compose">
        <div class="blog-editor-form-grid">
          <label for="blog-editor-title">Title</label>
          <input type="text" id="blog-editor-title" placeholder="Post title" />

          <label for="blog-editor-date">Date</label>
          <input type="date" id="blog-editor-date" />

          <label for="blog-editor-slug">Slug</label>
          <div class="blog-editor-slug-row">
            <input type="text" id="blog-editor-slug" placeholder="my-post-title" />
            <button type="button" data-editor-autoslug>Auto</button>
          </div>

          <label for="blog-editor-excerpt">Excerpt (Optional)</label>
          <textarea id="blog-editor-excerpt" rows="2" placeholder="Short summary"></textarea>
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
          <button type="button" data-editor-copy>Copy Markdown</button>
          <button type="button" data-editor-download>Download File</button>
          <button type="button" data-editor-open-github>Open GitHub Prefill</button>
        </div>
        <p class="blog-editor-status" data-editor-status aria-live="polite"></p>
      </div>

      <div class="blog-editor-render">
        <h4>Rendered Preview</h4>
        <div class="blog-editor-preview" data-editor-preview></div>
      </div>
    </div>
  </div>
</section>

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

    const expectedKeyHex = '{{ site.data.editor.guard }}'.trim().toLowerCase();
    const pbkdf2SaltHex = '{{ site.data.editor.grain }}'.trim().toLowerCase();
    const pbkdf2Iterations = Number('{{ site.data.editor.rounds }}') || 310000;
    const repo = shell.dataset.editorRepo || '';
    const branch = shell.dataset.editorBranch || 'master';

    if (!expectedKeyHex || !pbkdf2SaltHex || !pbkdf2Iterations) return;

    const panelView = shell.querySelector('[data-editor-panel]');
    const statusEl = shell.querySelector('[data-editor-status]');
    const lockBtn = shell.querySelector('[data-editor-lock-btn]');
    const titleInput = shell.querySelector('#blog-editor-title');
    const dateInput = shell.querySelector('#blog-editor-date');
    const slugInput = shell.querySelector('#blog-editor-slug');
    const excerptInput = shell.querySelector('#blog-editor-excerpt');
    const bodyInput = shell.querySelector('#blog-editor-body');
    const previewEl = shell.querySelector('[data-editor-preview]');
    const filenameEl = shell.querySelector('[data-editor-filename]');
    const autoslugBtn = shell.querySelector('[data-editor-autoslug]');
    const copyBtn = shell.querySelector('[data-editor-copy]');
    const downloadBtn = shell.querySelector('[data-editor-download]');
    const openGithubBtn = shell.querySelector('[data-editor-open-github]');

    let lastAutoSlug = '';
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

    function ensureSlug(force) {
      const candidate = slugify(titleInput.value);
      if (
        force ||
        !slugInput.value.trim() ||
        slugInput.value.trim() === lastAutoSlug
      ) {
        slugInput.value = candidate;
      }
      lastAutoSlug = candidate;
      return slugInput.value.trim() || candidate;
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
      const slug = ensureSlug(false);
      const excerpt = excerptInput.value.trim();
      const body = bodyInput.value.trim();

      if (!allowPartial && !title) throw new Error('Title is required.');
      if (!allowPartial && !body) throw new Error('Markdown body is required.');

      const effectiveTitle = title || 'Untitled Draft';
      const filename = date + '-' + slug + '.md';
      const frontMatter = [
        '---',
        'layout: post',
        'title: "' + yamlEscape(effectiveTitle) + '"',
        'date: ' + date
      ];

      if (excerpt) frontMatter.push('excerpt: "' + yamlEscape(excerpt) + '"');
      frontMatter.push('---', '');

      return {
        filename: filename,
        title: effectiveTitle,
        date: date,
        excerpt: excerpt,
        body: body,
        markdown: frontMatter.join('\n') + body + '\n'
      };
    }

    let previewTimer = null;
    function schedulePreview() {
      if (previewTimer) window.clearTimeout(previewTimer);
      previewTimer = window.setTimeout(updatePreview, 120);
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
            (built.excerpt ? '<p class="blog-editor-preview-excerpt">' + escapeHtml(built.excerpt) + '</p>' : '') +
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
      panelView.hidden = false;
      shellVisible = true;
      if (!dateInput.value) dateInput.value = todayString();
      ensureSlug(false);
      updatePreview();
      refreshPreviewWhenRenderersReady();
      titleInput.focus();
    }

    function hideShell() {
      shell.hidden = true;
      panelView.hidden = true;
      shellVisible = false;
      setStatus('', null);
    }

    async function requestUnlockAndShow() {
      if (shellVisible) return;

      const now = Date.now();
      if (now < blockedUntil) {
        window.alert('Draft console temporarily blocked. Try again in a minute.');
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
          window.alert('Unable to open draft console.');
          return;
        }

        failedAttempts = 0;
        showShell();
        setStatus('Draft tools unlocked.', 'success');
      } catch (err) {
        window.alert('Unable to open draft console.');
      }
    }

    function maybeRevealFromHash() {
      const hash = (window.location.hash || '').toLowerCase();
      if (hash === '#compose' || hash === '#draft') {
        requestUnlockAndShow();
      }
    }

    lockBtn.addEventListener('click', function() {
      hideShell();
    });

    autoslugBtn.addEventListener('click', function() {
      ensureSlug(true);
      schedulePreview();
    });

    titleInput.addEventListener('input', function() {
      ensureSlug(false);
      schedulePreview();
    });
    dateInput.addEventListener('input', schedulePreview);
    slugInput.addEventListener('input', schedulePreview);
    excerptInput.addEventListener('input', schedulePreview);
    bodyInput.addEventListener('input', schedulePreview);

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
      const key = (event.key || '').toLowerCase();
      if (key === 'e' && event.altKey && event.shiftKey) {
        event.preventDefault();
        requestUnlockAndShow();
      }
    });

    hideShell();
    maybeRevealFromHash();
  })();
</script>
{% endif %}

{% assign sorted_posts = site.posts | sort: 'date' | reverse %}
{% assign posts_by_year = sorted_posts | group_by_exp: "post", "post.date | date: '%Y'" %}
<article class="post-article blog-index-article">
{% if posts_by_year and posts_by_year != empty %}
  <ul class="blog-archive">
    {% for post in sorted_posts %}
    <li class="blog-archive-item">
      <a class="blog-archive-link" href="{{ post.url | relative_url }}">
        <h2 class="blog-archive-title">{{ post.title }}</h2>
      </a>
      <p class="blog-archive-date">{{ post.date | date: "%B %d, %Y" }}</p>
      {% assign preview = post.excerpt | strip_html | strip %}
      {% if preview != "" %}
      <p class="blog-archive-excerpt">{{ preview | truncate: 190 }}</p>
      {% endif %}
    </li>
    {% endfor %}
  </ul>
{% else %}
  <div class="blog-empty">
    <p>No posts yet — check back soon!</p>
    <p>
      To add one, create a Markdown file in the <code>_posts</code> directory named like
      <code>YYYY-MM-DD-title.md</code> with front matter:
    </p>
    <pre><code>---
layout: post
title: "My First Post"
---</code></pre>
  </div>
{% endif %}
</article>
