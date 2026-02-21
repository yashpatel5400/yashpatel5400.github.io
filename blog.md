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

    <label for="blog-editor-body">Markdown</label>
    <textarea id="blog-editor-body" rows="14" placeholder="Write your post in Markdown..."></textarea>

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

    <h4>Preview</h4>
    <div class="blog-editor-preview" data-editor-preview></div>
  </div>
</section>

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

    function buildPostContent() {
      const title = titleInput.value.trim();
      const date = ensureDate();
      const slug = ensureSlug(false);
      const excerpt = excerptInput.value.trim();
      const body = bodyInput.value.trim();

      if (!title) throw new Error('Title is required.');
      if (!body) throw new Error('Markdown body is required.');

      const filename = date + '-' + slug + '.md';
      const frontMatter = [
        '---',
        'layout: post',
        'title: "' + yamlEscape(title) + '"',
        'date: ' + date
      ];

      if (excerpt) frontMatter.push('excerpt: "' + yamlEscape(excerpt) + '"');
      frontMatter.push('---', '');

      return {
        filename: filename,
        markdown: frontMatter.join('\n') + body + '\n'
      };
    }

    function safePreviewMarkdown(rawMarkdown) {
      const escaped = rawMarkdown
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
      return '<pre>' + escaped + '</pre>';
    }

    function updatePreview() {
      try {
        const built = buildPostContent();
        filenameEl.textContent = built.filename;
        previewEl.innerHTML = safePreviewMarkdown(built.markdown);
        setStatus('', null);
      } catch (err) {
        filenameEl.textContent = 'YYYY-MM-DD-my-post.md';
        previewEl.innerHTML = '<p class="blog-editor-preview-empty">Add a title and markdown body to preview.</p>';
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
      updatePreview();
    });

    titleInput.addEventListener('input', function() {
      ensureSlug(false);
      updatePreview();
    });
    dateInput.addEventListener('input', updatePreview);
    slugInput.addEventListener('input', updatePreview);
    excerptInput.addEventListener('input', updatePreview);
    bodyInput.addEventListener('input', updatePreview);

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
