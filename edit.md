---
layout: default
title: Edit
permalink: /edit/
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
    <button
      type="button"
      class="blog-editor-global-sidebar-toggle"
      data-editor-sidebar-toggle
      aria-label="Toggle sidebar"
      aria-expanded="true"
    >
      <span></span>
      <span></span>
      <span></span>
      <span class="sr-only">Toggle sidebar</span>
    </button>
    <div class="blog-editor-workbench">
      <aside class="blog-editor-sidebar">
        <div class="blog-editor-library">
          <div class="blog-editor-library-head">
            <h5>Workspace</h5>
            <div class="blog-editor-library-head-actions">
              <button type="button" data-editor-new-draft>New Draft</button>
            </div>
          </div>

          <div class="blog-editor-library-columns">
            <div class="blog-editor-library-pane">
              <div class="blog-editor-library-pane-head">
                <h6>Drafts</h6>
              </div>
              <ul class="blog-editor-entity-list" data-editor-draft-list></ul>
            </div>

            <div class="blog-editor-library-pane">
              <div class="blog-editor-library-pane-head">
                <h6>Published</h6>
              </div>
              <ul class="blog-editor-entity-list" data-editor-post-list></ul>
            </div>
          </div>
        </div>
      </aside>

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
          <div class="blog-editor-meta-actions">
            <button type="button" data-editor-save>Save</button>
            <button type="button" data-editor-publish>Publish</button>
          </div>
        </div>

        <p class="blog-editor-context" data-editor-context></p>

        <label for="blog-editor-body">Markdown / LaTeX</label>
        <textarea
          id="blog-editor-body"
          class="blog-editor-body-input"
          rows="20"
          placeholder="Write markdown and equations like $\\alpha$ or $$\\int_0^1 x^2 dx$$..."
        ></textarea>
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
    const draftApiBase = (shell.dataset.draftApiBase || '').trim().replace(/\/+$/, '');
    const draftApiAuthMode = (shell.dataset.draftApiAuth || 'session').trim().toLowerCase();
    const defaultDraftId = (shell.dataset.draftId || 'main').trim();
    const sessionUnlockEnabled = draftApiAuthMode === 'session' && Boolean(draftApiBase);
    const localUnlockEnabled = Boolean(expectedKeyHex && pbkdf2SaltHex && pbkdf2Iterations) && !sessionUnlockEnabled;

    const statusEl = shell.querySelector('[data-editor-status]');
    const newDraftBtn = shell.querySelector('[data-editor-new-draft]');
    const sidebarToggleBtn = shell.querySelector('[data-editor-sidebar-toggle]');
    const draftListEl = shell.querySelector('[data-editor-draft-list]');
    const postListEl = shell.querySelector('[data-editor-post-list]');
    const contextEl = shell.querySelector('[data-editor-context]');

    const titleInput = shell.querySelector('#blog-editor-title');
    const dateInput = shell.querySelector('#blog-editor-date');
    const bodyInput = shell.querySelector('#blog-editor-body');
    const previewEl = shell.querySelector('[data-editor-preview]');
    const saveBtn = shell.querySelector('[data-editor-save]');
    const publishBtn = shell.querySelector('[data-editor-publish]');

    const draftSnapshotKey = 'make-post-draft-snapshot-v2';
    const draftApiTokenStorageKey = 'make-post-draft-api-token-v1';
    const draftApiTokenPersistentStorageKey = 'make-post-draft-api-token-persist-v1';
    const sidebarCollapsedStorageKey = 'edit-sidebar-collapsed-v1';

    const state = {
      shellVisible: false,
      failedAttempts: 0,
      blockedUntil: 0,
      currentDraftId: defaultDraftId || 'main',
      sourcePostFilename: '',
      drafts: [],
      posts: []
    };

    function getSidebarCollapsedPreference() {
      try {
        return window.localStorage.getItem(sidebarCollapsedStorageKey) === '1';
      } catch (err) {
        return false;
      }
    }

    function applySidebarCollapsed(collapsed) {
      const isCollapsed = Boolean(collapsed);
      shell.classList.toggle('is-sidebar-collapsed', isCollapsed);
      if (sidebarToggleBtn) {
        sidebarToggleBtn.setAttribute('aria-expanded', isCollapsed ? 'false' : 'true');
      }
      try {
        window.localStorage.setItem(sidebarCollapsedStorageKey, isCollapsed ? '1' : '0');
      } catch (err) {
        // no-op
      }
    }

    function toggleSidebar() {
      applySidebarCollapsed(!shell.classList.contains('is-sidebar-collapsed'));
    }

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

    function generateDraftId() {
      return 'draft-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 8);
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

    async function parseErrorMessage(response) {
      try {
        const payload = await response.json();
        if (payload && typeof payload.error === 'string') return payload.error;
      } catch (err) {
        // no-op
      }
      return 'Draft DB request failed.';
    }

    function delay(ms) {
      return new Promise(function(resolve) {
        window.setTimeout(resolve, ms);
      });
    }

    async function fetchWithRetry(url, request, retryCount) {
      const attempts = Math.max(1, Number(retryCount) || 1);
      let lastError = null;

      for (let i = 0; i < attempts; i += 1) {
        try {
          const response = await fetch(url, request);
          if ((response.status >= 500 || response.status === 429) && i + 1 < attempts) {
            await delay(350 * (i + 1));
            continue;
          }
          return response;
        } catch (err) {
          lastError = err;
          if (i + 1 < attempts) {
            await delay(350 * (i + 1));
            continue;
          }
        }
      }

      throw lastError || new Error('Request failed.');
    }

    async function requestSessionToken(passphrase) {
      const response = await fetchWithRetry(draftApiBase + '/api/session', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ passphrase: passphrase })
      }, 3);
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
        return requestSessionToken(passphraseInput.trim());
      }

      const tokenInput = window.prompt('Draft DB token');
      if (!tokenInput || !tokenInput.trim()) return '';
      const token = tokenInput.trim();
      setStoredApiToken(token);
      return token;
    }

    async function apiRequest(path, options, promptForToken, passphraseHint) {
      if (!hasDraftApiConfigured()) return null;
      let token = getStoredApiToken();
      if (!token && promptForToken) {
        token = await ensureApiToken(true, passphraseHint);
      }
      if (!token) return null;

      const request = Object.assign({}, options || {});
      const headers = Object.assign({}, request.headers || {});
      headers.Authorization = 'Bearer ' + token;
      if (!headers['Content-Type'] && request.body) {
        headers['Content-Type'] = 'application/json';
      }
      request.headers = headers;

      let response = await fetchWithRetry(draftApiBase + path, request, 2);
      if (response.status === 401 && promptForToken) {
        setStoredApiToken('');
        token = await ensureApiToken(true, passphraseHint);
        if (!token) return null;
        request.headers.Authorization = 'Bearer ' + token;
        response = await fetchWithRetry(draftApiBase + path, request, 2);
      }
      return response;
    }

    function buildPostContent(allowPartial) {
      const title = titleInput.value.trim();
      const date = ensureDate();
      const slug = slugify(title);
      const body = bodyInput.value.trim();

      if (!allowPartial && !title) throw new Error('Title is required.');
      if (!allowPartial && !body) throw new Error('Markdown body is required.');

      const effectiveTitle = title || 'Untitled Draft';
      const filename = state.sourcePostFilename || (date + '-' + slug + '.md');
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

    function setDraftSnapshotLocal(showMessage) {
      try {
        const payload = {
          draftId: state.currentDraftId,
          sourcePostFilename: state.sourcePostFilename,
          title: titleInput.value,
          date: dateInput.value,
          body: bodyInput.value,
          savedAt: new Date().toISOString()
        };
        window.localStorage.setItem(draftSnapshotKey, JSON.stringify(payload));
        if (showMessage) setStatus('Draft saved locally.', 'success');
        return true;
      } catch (err) {
        if (showMessage) setStatus('Unable to save draft in this browser.', 'error');
        return false;
      }
    }

    function loadDraftSnapshotLocal(showMessage) {
      try {
        const raw = window.localStorage.getItem(draftSnapshotKey);
        if (!raw) return false;
        const payload = JSON.parse(raw);
        if (!payload || typeof payload !== 'object') return false;

        if (typeof payload.draftId === 'string' && payload.draftId.trim()) {
          state.currentDraftId = payload.draftId.trim();
        }
        if (typeof payload.sourcePostFilename === 'string') {
          state.sourcePostFilename = payload.sourcePostFilename.trim();
        }
        if (typeof payload.title === 'string') titleInput.value = payload.title;
        if (typeof payload.date === 'string') dateInput.value = payload.date;
        if (typeof payload.body === 'string') bodyInput.value = payload.body;
        if (!dateInput.value) dateInput.value = todayString();

        if (showMessage) setStatus('Draft restored from local save.', 'success');
        return true;
      } catch (err) {
        if (showMessage) setStatus('Saved draft could not be restored.', 'error');
        return false;
      }
    }

    function applyEditorRecord(record) {
      if (!record || typeof record !== 'object') return;
      if (typeof record.title === 'string') titleInput.value = record.title;
      if (typeof record.draft_date === 'string' && record.draft_date) {
        dateInput.value = record.draft_date;
      } else if (typeof record.date === 'string' && record.date) {
        dateInput.value = record.date;
      }
      if (typeof record.body === 'string') bodyInput.value = record.body;
      if (!dateInput.value) dateInput.value = todayString();

      if (typeof record.source_post_filename === 'string') {
        state.sourcePostFilename = record.source_post_filename.trim();
      }
    }

    function updateContextLabel() {
      if (!contextEl) return;
      if (state.sourcePostFilename) {
        contextEl.textContent = 'Editing published post';
        return;
      }
      contextEl.textContent = 'Editing draft: ' + state.currentDraftId;
    }

    function formatShortTimestamp(value) {
      if (!value) return '';
      const parsed = new Date(value);
      if (Number.isNaN(parsed.getTime())) return '';
      return parsed.toLocaleString(undefined, {
        month: 'short',
        day: 'numeric',
        hour: 'numeric',
        minute: '2-digit'
      });
    }

    function renderDraftList() {
      if (!draftListEl) return;
      draftListEl.innerHTML = '';
      if (!state.drafts.length) {
        const emptyItem = document.createElement('li');
        emptyItem.className = 'blog-editor-entity-empty';
        emptyItem.textContent = 'No drafts yet.';
        draftListEl.appendChild(emptyItem);
        return;
      }

      state.drafts.forEach(function(draft) {
        const li = document.createElement('li');
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'blog-editor-entity-btn';
        btn.setAttribute('data-draft-id', draft.draft_id || '');

        if ((draft.draft_id || '') === state.currentDraftId && !state.sourcePostFilename) {
          btn.classList.add('is-active');
        }

        const title = (draft.title || '').trim() || 'Untitled Draft';
        const dateLabel = draft.draft_date || '';
        const tsLabel = formatShortTimestamp(draft.updated_at);
        const metaParts = [dateLabel, tsLabel].filter(Boolean);

        btn.innerHTML =
          '<span class="blog-editor-entity-title">' + escapeHtml(title) + '</span>' +
          '<span class="blog-editor-entity-meta">' + escapeHtml(metaParts.join(' · ')) + '</span>';

        li.appendChild(btn);
        draftListEl.appendChild(li);
      });
    }

    function renderPostList() {
      if (!postListEl) return;
      postListEl.innerHTML = '';
      if (!state.posts.length) {
        const emptyItem = document.createElement('li');
        emptyItem.className = 'blog-editor-entity-empty';
        emptyItem.textContent = 'No published posts found.';
        postListEl.appendChild(emptyItem);
        return;
      }

      state.posts.forEach(function(post) {
        const li = document.createElement('li');
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'blog-editor-entity-btn';
        btn.setAttribute('data-post-filename', post.filename || '');
        if ((post.filename || '') === state.sourcePostFilename) {
          btn.classList.add('is-active');
        }

        const title = (post.title || '').trim() || 'Untitled Post';
        const dateLabel = post.date || '';

        btn.innerHTML =
          '<span class="blog-editor-entity-title">' + escapeHtml(title) + '</span>' +
          '<span class="blog-editor-entity-meta">' + escapeHtml(dateLabel) + '</span>';

        li.appendChild(btn);
        postListEl.appendChild(li);
      });
    }

    async function fetchDraftList(promptForToken) {
      const response = await apiRequest('/api/drafts', { method: 'GET' }, promptForToken);
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      state.drafts = Array.isArray(payload && payload.drafts) ? payload.drafts : [];
      renderDraftList();
      return true;
    }

    async function fetchPostList(promptForToken) {
      const response = await apiRequest('/api/posts', { method: 'GET' }, promptForToken);
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      state.posts = Array.isArray(payload && payload.posts) ? payload.posts : [];
      renderPostList();
      return true;
    }

    async function refreshLibrary(promptForToken) {
      let draftsError = null;
      let postsError = null;

      try {
        await fetchDraftList(promptForToken);
      } catch (err) {
        draftsError = err;
        state.drafts = [];
        renderDraftList();
      }

      try {
        await fetchPostList(promptForToken);
      } catch (err) {
        postsError = err;
        state.posts = [];
        renderPostList();
      }

      if (draftsError && postsError) {
        throw draftsError;
      }
      return { draftsError: draftsError, postsError: postsError };
    }

    async function loadDraftRemoteById(draftId, showMessage, promptForToken) {
      if (!draftId) return false;
      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(draftId),
        { method: 'GET' },
        promptForToken
      );
      if (response === null) return false;
      if (response.status === 404) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      const draft = payload && payload.draft ? payload.draft : null;
      if (!draft || typeof draft !== 'object') return false;

      state.currentDraftId = draftId;
      applyEditorRecord(draft);
      updatePreview();
      updateContextLabel();
      setDraftSnapshotLocal(false);
      renderDraftList();
      renderPostList();
      if (showMessage) setStatus('Draft loaded from database.', 'success');
      return true;
    }

    async function loadPublishedPost(filename, showMessage, promptForToken) {
      if (!filename) return false;
      const response = await apiRequest(
        '/api/posts/' + encodeURIComponent(filename),
        { method: 'GET' },
        promptForToken
      );
      if (response === null) return false;
      if (response.status === 404) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      const payload = await response.json();
      const post = payload && payload.post ? payload.post : null;
      if (!post || typeof post !== 'object') return false;

      const matchingDraft = state.drafts.find(function(item) {
        return (item && item.source_post_filename) === filename;
      });
      if (matchingDraft && matchingDraft.draft_id) {
        state.currentDraftId = matchingDraft.draft_id;
      } else {
        state.currentDraftId = generateDraftId();
      }

      state.sourcePostFilename = filename;
      applyEditorRecord(post);
      updatePreview();
      updateContextLabel();
      setDraftSnapshotLocal(false);
      renderDraftList();
      renderPostList();
      if (showMessage) setStatus('Loaded published post for editing.', 'success');
      return true;
    }

    async function saveDraftRemote(showMessage, promptForToken, passphraseHint) {
      if (!hasDraftApiConfigured()) return false;
      const built = buildPostContent(true);
      const payload = {
        title: titleInput.value,
        date: ensureDate(),
        body: bodyInput.value,
        filename: built.filename,
        markdown: built.markdown,
        source_post_filename: state.sourcePostFilename
      };

      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(state.currentDraftId),
        { method: 'PUT', body: JSON.stringify(payload) },
        promptForToken,
        passphraseHint
      );
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      const result = await response.json();
      if (result && result.draft && typeof result.draft.source_post_filename === 'string') {
        state.sourcePostFilename = result.draft.source_post_filename;
      }

      await fetchDraftList(false).catch(function() {
        // no-op
      });
      updateContextLabel();
      renderDraftList();
      renderPostList();
      if (showMessage) setStatus('Draft saved to database.', 'success');
      return true;
    }

    async function publishPost(passphraseHint) {
      if (!hasDraftApiConfigured()) {
        throw new Error('Draft DB URL is not configured in _data/editor.yml.');
      }

      const built = buildPostContent(false);
      const payload = {
        title: built.title,
        date: built.date,
        body: built.body,
        filename: state.sourcePostFilename || built.filename,
        source_draft_id: state.currentDraftId
      };

      const response = await apiRequest(
        '/api/publish',
        { method: 'POST', body: JSON.stringify(payload) },
        true,
        passphraseHint
      );
      if (response === null) {
        throw new Error('Authentication is required to publish.');
      }
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      const result = await response.json();
      const post = result && result.post ? result.post : null;
      if (!post || typeof post !== 'object') {
        throw new Error('Publish response was invalid.');
      }

      state.sourcePostFilename = post.filename || state.sourcePostFilename;
      titleInput.value = post.title || titleInput.value;
      dateInput.value = post.date || dateInput.value;
      bodyInput.value = post.body || bodyInput.value;

      setDraftSnapshotLocal(false);
      updatePreview();
      updateContextLabel();

      await refreshLibrary(false).catch(function() {
        // no-op
      });

      const blogLink = post.html_url || ('{{ "/blog/" | relative_url }}');
      setStatus('Published. It will appear on /blog/ after GitHub Pages rebuilds. ' + blogLink, 'success');
      return true;
    }

    function startNewDraft(showMessage) {
      setDraftSnapshotLocal(false);
      state.currentDraftId = generateDraftId();
      state.sourcePostFilename = '';
      titleInput.value = '';
      dateInput.value = todayString();
      bodyInput.value = '';
      updatePreview();
      updateContextLabel();
      renderDraftList();
      renderPostList();
      setDraftSnapshotLocal(false);
      if (showMessage) setStatus('Started a new draft.', 'success');
      titleInput.focus();
    }

    let previewTimer = null;
    let autosaveTimer = null;
    function schedulePreview() {
      if (previewTimer) window.clearTimeout(previewTimer);
      previewTimer = window.setTimeout(updatePreview, 120);
    }

    function scheduleAutosave() {
      if (autosaveTimer) window.clearTimeout(autosaveTimer);
      autosaveTimer = window.setTimeout(function() {
        setDraftSnapshotLocal(false);
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

        previewEl.innerHTML =
          '<article class="blog-editor-preview-article">' +
            '<h1 class="blog-editor-preview-title">' + escapeHtml(built.title) + '</h1>' +
            (dateLabel ? '<p class="blog-editor-preview-date">' + escapeHtml(dateLabel) + '</p>' : '') +
            '<div class="post-content blog-editor-preview-content">' + renderedBody + '</div>' +
          '</article>';

        renderMathInPreview();
      } catch (err) {
        previewEl.innerHTML = '<p class="blog-editor-preview-empty">Unable to render preview.</p>';
        setStatus(err && err.message ? err.message : 'Unable to render preview.', 'error');
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
      state.shellVisible = true;

      loadDraftSnapshotLocal(false);
      if (!state.currentDraftId) {
        state.currentDraftId = defaultDraftId || 'main';
      }
      if (!dateInput.value) dateInput.value = todayString();

      if (hasDraftApiConfigured() && getStoredApiToken()) {
        try {
          await refreshLibrary(false);
          const loadedCurrent = await loadDraftRemoteById(state.currentDraftId, false, false);
          if (!loadedCurrent && state.drafts.length) {
            await loadDraftRemoteById(state.drafts[0].draft_id, false, false);
          }
        } catch (err) {
          // no-op
        }
      } else {
        renderDraftList();
        renderPostList();
      }

      updateContextLabel();
      updatePreview();
      refreshPreviewWhenRenderersReady();
      titleInput.focus();
    }

    function hideShell() {
      setDraftSnapshotLocal(false);
      shell.hidden = true;
      if (lockState) lockState.hidden = false;
      state.shellVisible = false;
      setStatus('', null);
    }

    async function requestUnlockAndShow(options) {
      const opts = options && typeof options === 'object' ? options : {};
      const allowPrompt = opts.allowPrompt !== false;
      const silent = opts.silent === true;
      if (state.shellVisible) return;

      const hasSessionUnlock = hasDraftApiConfigured() && isSessionAuthMode();
      if (!localUnlockEnabled && !hasSessionUnlock) {
        if (!silent) window.alert('Editor authentication is not configured.');
        return;
      }

      const now = Date.now();
      if (now < state.blockedUntil) {
        if (!silent) window.alert('Editor temporarily blocked. Try again in a minute.');
        return;
      }

      if (hasSessionUnlock) {
        const existingToken = getStoredApiToken();
        if (existingToken) {
          try {
            await refreshLibrary(false);
            state.failedAttempts = 0;
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

      if (!allowPrompt) return;

      const passphrase = window.prompt('Passphrase');
      if (passphrase === null || !passphrase.trim()) return;

      try {
        const normalizedPassphrase = passphrase.trim();

        if (localUnlockEnabled) {
          const derivedHex = await derivePassphraseKeyHex(normalizedPassphrase);
          if (derivedHex !== expectedKeyHex) {
            state.failedAttempts += 1;
            if (state.failedAttempts >= 5) {
              state.failedAttempts = 0;
              state.blockedUntil = Date.now() + 60000;
            }
            if (!silent) window.alert('Unable to open editor.');
            return;
          }
        }

        if (hasSessionUnlock) {
          const token = await ensureApiToken(false, normalizedPassphrase);
          if (!token) {
            state.failedAttempts += 1;
            if (state.failedAttempts >= 5) {
              state.failedAttempts = 0;
              state.blockedUntil = Date.now() + 60000;
            }
            if (!silent) window.alert('Unable to open editor.');
            return;
          }
        }

        state.failedAttempts = 0;
        await showShell();
        setStatus('Editor unlocked.', 'success');
      } catch (err) {
        if (!silent) window.alert('Unable to open editor.');
      }
    }

    function maybeRevealFromHash() {
      const hash = (window.location.hash || '').toLowerCase();
      if (hash === '#compose' || hash === '#draft') {
        requestUnlockAndShow({ allowPrompt: true, silent: false });
      }
    }

    async function maybeAutoUnlockFromStoredCredentials() {
      const hash = (window.location.hash || '').toLowerCase();
      if (hash === '#compose' || hash === '#draft') return;
      if (!hasDraftApiConfigured() || !isSessionAuthMode()) return;
      if (!getStoredApiToken()) return;
      await requestUnlockAndShow({ allowPrompt: false, silent: true });
    }

    function isComposeShortcut(event) {
      const key = (event.key || '').toLowerCase();
      if (key !== 'e' || !event.shiftKey) return false;
      return event.altKey || event.metaKey;
    }

    if (unlockBtn) {
      unlockBtn.addEventListener('click', function() {
        requestUnlockAndShow({ allowPrompt: true, silent: false });
      });
    }

    if (newDraftBtn) {
      newDraftBtn.addEventListener('click', function() {
        startNewDraft(true);
      });
    }

    if (sidebarToggleBtn) {
      sidebarToggleBtn.addEventListener('click', function() {
        toggleSidebar();
      });
    }

    if (draftListEl) {
      draftListEl.addEventListener('click', async function(event) {
        const target = event.target && event.target.closest('[data-draft-id]');
        if (!target) return;
        const selectedId = (target.getAttribute('data-draft-id') || '').trim();
        if (!selectedId) return;
        try {
          const loaded = await loadDraftRemoteById(selectedId, true, true);
          if (!loaded) {
            setStatus('Draft not found.', 'error');
          }
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to load draft.', 'error');
        }
      });
    }

    if (postListEl) {
      postListEl.addEventListener('click', async function(event) {
        const target = event.target && event.target.closest('[data-post-filename]');
        if (!target) return;
        const filename = (target.getAttribute('data-post-filename') || '').trim();
        if (!filename) return;
        try {
          const loaded = await loadPublishedPost(filename, true, true);
          if (!loaded) {
            setStatus('Published post not found.', 'error');
          }
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to load published post.', 'error');
        }
      });
    }

    if (saveBtn) {
      saveBtn.addEventListener('click', async function() {
        const localSaved = setDraftSnapshotLocal(false);
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
            setStatus('Saved locally. Authentication is required for backend save.', 'error');
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

    if (publishBtn) {
      publishBtn.addEventListener('click', async function() {
        const localSaved = setDraftSnapshotLocal(false);
        try {
          if (hasDraftApiConfigured()) {
            await saveDraftRemote(false, true).catch(function() {
              // continue with publish attempt
            });
          }
          await publishPost();
          if (!localSaved) {
            setDraftSnapshotLocal(false);
          }
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to publish post.', 'error');
        }
      });
    }

    titleInput.addEventListener('input', onEditorInput);
    dateInput.addEventListener('input', onEditorInput);
    bodyInput.addEventListener('input', onEditorInput);

    document.addEventListener('keydown', function(event) {
      if (isComposeShortcut(event)) {
        event.preventDefault();
        requestUnlockAndShow({ allowPrompt: true, silent: false });
      }
    });

    window.addEventListener('hashchange', maybeRevealFromHash);
    window.addEventListener('beforeunload', function() {
      if (state.shellVisible) setDraftSnapshotLocal(false);
    });

    hideShell();
    applySidebarCollapsed(getSidebarCollapsedPreference());
    maybeRevealFromHash();
    maybeAutoUnlockFromStoredCredentials().catch(function() {
      // no-op
    });
  })();
</script>
{% endif %}
