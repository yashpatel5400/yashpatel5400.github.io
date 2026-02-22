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
                <h6>Saves</h6>
              </div>
              <ul class="blog-editor-entity-list" data-editor-autosave-list></ul>
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
            <button type="button" data-editor-open-preview>Preview</button>
            <button type="button" data-editor-share-preview>Share</button>
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
    const autosaveListEl = shell.querySelector('[data-editor-autosave-list]');
    const postListEl = shell.querySelector('[data-editor-post-list]');
    const contextEl = shell.querySelector('[data-editor-context]');
    const composePane = shell.querySelector('.blog-editor-compose');

    const titleInput = shell.querySelector('#blog-editor-title');
    const dateInput = shell.querySelector('#blog-editor-date');
    const bodyInput = shell.querySelector('#blog-editor-body');
    const previewEl = shell.querySelector('[data-editor-preview]');
    const saveBtn = shell.querySelector('[data-editor-save]');
    const fullPreviewBtn = shell.querySelector('[data-editor-open-preview]');
    const sharePreviewBtn = shell.querySelector('[data-editor-share-preview]');
    const publishBtn = shell.querySelector('[data-editor-publish]');
    const saveButtonDefaultLabel = saveBtn ? (saveBtn.textContent || 'Save') : 'Save';

    const draftSnapshotKey = 'make-post-draft-snapshot-v2';
    const draftApiTokenStorageKey = 'make-post-draft-api-token-v1';
    const draftApiTokenPersistentStorageKey = 'make-post-draft-api-token-persist-v1';
    const sidebarCollapsedStorageKey = 'edit-sidebar-collapsed-v1';
    const autosaveIntervalMs = 12000;
    const autosaveListLimit = 100;

    const state = {
      shellVisible: false,
      failedAttempts: 0,
      blockedUntil: 0,
      currentDraftId: defaultDraftId || 'main',
      sourcePostFilename: '',
      drafts: [],
      autosaves: [],
      posts: [],
      lastAutosaveFingerprint: '',
      autosaveInFlight: false
    };
    let saveButtonFeedbackTimer = null;
    let saveActionInFlight = false;

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

    function isEditingPublishedPost() {
      return Boolean(state.sourcePostFilename);
    }

    function updatePublishActionLabel() {
      if (!publishBtn) return;
      publishBtn.textContent = isEditingPublishedPost() ? 'Update' : 'Publish';
    }

    function autosaveFingerprint() {
      return [
        state.currentDraftId || '',
        state.sourcePostFilename || '',
        titleInput.value || '',
        dateInput.value || '',
        bodyInput.value || ''
      ].join('\u0001');
    }

    function markAutosaveBaseline() {
      state.lastAutosaveFingerprint = autosaveFingerprint();
    }

    function setStatus(message, kind) {
      if (!statusEl) return;
      statusEl.textContent = message;
      statusEl.classList.remove('is-error', 'is-success');
      if (kind) statusEl.classList.add(kind === 'error' ? 'is-error' : 'is-success');
    }

    function clearSaveButtonFeedbackTimer() {
      if (saveButtonFeedbackTimer) {
        window.clearTimeout(saveButtonFeedbackTimer);
        saveButtonFeedbackTimer = null;
      }
    }

    function setSaveButtonState(stateName) {
      if (!saveBtn) return;
      clearSaveButtonFeedbackTimer();

      if (stateName === 'saving') {
        saveBtn.textContent = 'Saving...';
        saveBtn.disabled = true;
        return;
      }

      if (stateName === 'saved') {
        saveBtn.textContent = 'Saved!';
        saveBtn.disabled = false;
        saveButtonFeedbackTimer = window.setTimeout(function() {
          saveBtn.textContent = saveButtonDefaultLabel;
          saveBtn.disabled = false;
          saveButtonFeedbackTimer = null;
        }, 1400);
        return;
      }

      if (stateName === 'error') {
        saveBtn.textContent = 'Save Failed';
        saveBtn.disabled = false;
        saveButtonFeedbackTimer = window.setTimeout(function() {
          saveBtn.textContent = saveButtonDefaultLabel;
          saveBtn.disabled = false;
          saveButtonFeedbackTimer = null;
        }, 1700);
        return;
      }

      saveBtn.textContent = saveButtonDefaultLabel;
      saveBtn.disabled = false;
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
      if (!previewEl) return;
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
      syncLockVisibility();
    }

    function shouldHideLockRow() {
      if (state.shellVisible) return true;
      if (!hasDraftApiConfigured() || !isSessionAuthMode()) return false;
      return Boolean(getStoredApiToken());
    }

    function syncLockVisibility() {
      if (!lockState) return;
      lockState.hidden = shouldHideLockRow();
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

      if (!state.sourcePostFilename && typeof record.filename === 'string') {
        const candidateFilename = record.filename.trim();
        const isPublished = state.posts.some(function(post) {
          return post && post.filename === candidateFilename;
        });
        if (candidateFilename && isPublished) {
          state.sourcePostFilename = candidateFilename;
        }
      }
    }

    function updateContextLabel() {
      if (!contextEl) return;
      if (state.sourcePostFilename) {
        contextEl.textContent = 'Editing published post';
      } else {
        contextEl.textContent = 'Editing draft: ' + state.currentDraftId;
      }
      updatePublishActionLabel();
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
        const row = document.createElement('div');
        row.className = 'blog-editor-entity-row';

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

        const deleteBtn = document.createElement('button');
        deleteBtn.type = 'button';
        deleteBtn.className = 'blog-editor-entity-delete';
        deleteBtn.setAttribute('data-delete-draft-id', draft.draft_id || '');
        deleteBtn.setAttribute('aria-label', 'Delete draft "' + title + '"');
        deleteBtn.textContent = '🗑️';
        deleteBtn.disabled = !draft.draft_id;

        row.appendChild(btn);
        row.appendChild(deleteBtn);
        li.appendChild(row);
        draftListEl.appendChild(li);
      });
    }

    function renderAutosaveList() {
      if (!autosaveListEl) return;
      autosaveListEl.innerHTML = '';
      if (!state.currentDraftId) {
        const emptyItem = document.createElement('li');
        emptyItem.className = 'blog-editor-entity-empty';
        emptyItem.textContent = 'No draft selected.';
        autosaveListEl.appendChild(emptyItem);
        return;
      }
      if (!state.autosaves.length) {
        const emptyItem = document.createElement('li');
        emptyItem.className = 'blog-editor-entity-empty';
        emptyItem.textContent = 'No saves yet.';
        autosaveListEl.appendChild(emptyItem);
        return;
      }

      state.autosaves.forEach(function(autosave) {
        const li = document.createElement('li');
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'blog-editor-entity-btn';
        btn.setAttribute('data-autosave-id', String(autosave.autosave_id || ''));

        const title = (autosave.title || '').trim() || 'Untitled Draft';
        const dateLabel = autosave.draft_date || '';
        const tsLabel = formatShortTimestamp(autosave.saved_at);
        const metaParts = [dateLabel, tsLabel].filter(Boolean);

        btn.innerHTML =
          '<span class="blog-editor-entity-title">' + escapeHtml(title) + '</span>' +
          '<span class="blog-editor-entity-meta">' + escapeHtml(metaParts.join(' · ')) + '</span>';

        li.appendChild(btn);
        autosaveListEl.appendChild(li);
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
        const row = document.createElement('div');
        row.className = 'blog-editor-entity-row';

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

        const deleteBtn = document.createElement('button');
        deleteBtn.type = 'button';
        deleteBtn.className = 'blog-editor-entity-delete';
        deleteBtn.setAttribute('data-delete-post-filename', post.filename || '');
        deleteBtn.setAttribute('aria-label', 'Delete published post "' + title + '"');
        deleteBtn.textContent = '🗑️';
        deleteBtn.disabled = !post.filename;

        row.appendChild(btn);
        row.appendChild(deleteBtn);
        li.appendChild(row);
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

    async function fetchAutosaveList(promptForToken) {
      if (!state.currentDraftId || !hasDraftApiConfigured()) {
        state.autosaves = [];
        renderAutosaveList();
        return false;
      }
      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(state.currentDraftId) + '/autosaves?limit=' + autosaveListLimit,
        { method: 'GET' },
        promptForToken
      );
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      state.autosaves = Array.isArray(payload && payload.autosaves) ? payload.autosaves : [];
      renderAutosaveList();
      return true;
    }

    async function loadAutosaveById(autosaveId, showMessage, promptForToken) {
      if (!autosaveId || !state.currentDraftId || !hasDraftApiConfigured()) return false;
      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(state.currentDraftId) + '/autosaves/' + encodeURIComponent(String(autosaveId)),
        { method: 'GET' },
        promptForToken
      );
      if (response === null) return false;
      if (response.status === 404) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const payload = await response.json();
      const autosave = payload && payload.autosave ? payload.autosave : null;
      if (!autosave || typeof autosave !== 'object') return false;

      applyEditorRecord(autosave);
      updatePreview();
      updateContextLabel();
      setDraftSnapshotLocal(false);
      markAutosaveBaseline();
      if (showMessage) setStatus('Loaded saved version.', 'success');
      return true;
    }

    async function deleteDraftRemote(draftId, promptForToken) {
      if (!draftId || !hasDraftApiConfigured()) return false;
      const response = await apiRequest(
        '/api/drafts/' + encodeURIComponent(draftId),
        { method: 'DELETE' },
        promptForToken
      );
      if (response === null) return false;
      if (response.status === 404) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      state.drafts = state.drafts.filter(function(item) {
        return item && item.draft_id !== draftId;
      });
      renderDraftList();
      return true;
    }

    async function deletePublishedPostRemote(filename, promptForToken) {
      if (!filename || !hasDraftApiConfigured()) return false;
      const response = await apiRequest(
        '/api/posts/' + encodeURIComponent(filename),
        { method: 'DELETE' },
        promptForToken
      );
      if (response === null) return false;
      if (response.status === 404) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      state.posts = state.posts.filter(function(item) {
        return item && item.filename !== filename;
      });
      if (state.sourcePostFilename === filename) {
        state.sourcePostFilename = '';
      }
      renderPostList();
      updateContextLabel();

      await fetchDraftList(false).catch(function() {
        // no-op
      });
      renderDraftList();
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
      await fetchAutosaveList(false).catch(function() {
        state.autosaves = [];
        renderAutosaveList();
      });
      markAutosaveBaseline();
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
      await fetchAutosaveList(false).catch(function() {
        state.autosaves = [];
        renderAutosaveList();
      });
      markAutosaveBaseline();
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
      await fetchAutosaveList(false).catch(function() {
        // no-op
      });
      updateContextLabel();
      renderDraftList();
      renderPostList();
      markAutosaveBaseline();
      if (showMessage) setStatus('Draft saved to database.', 'success');
      return true;
    }

    async function createAutosaveRemote(promptForToken) {
      if (!hasDraftApiConfigured() || !state.currentDraftId) return false;
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
        '/api/drafts/' + encodeURIComponent(state.currentDraftId) + '/autosaves',
        { method: 'POST', body: JSON.stringify(payload) },
        promptForToken
      );
      if (response === null) return false;
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }
      const result = await response.json().catch(function() {
        return null;
      });
      if (result && result.autosave && typeof result.autosave.source_post_filename === 'string') {
        state.sourcePostFilename = result.autosave.source_post_filename;
      }
      await fetchDraftList(false).catch(function() {
        // no-op
      });
      await fetchAutosaveList(false).catch(function() {
        // no-op
      });
      updateContextLabel();
      renderDraftList();
      renderPostList();
      markAutosaveBaseline();
      return true;
    }

    async function publishPost(passphraseHint) {
      if (!hasDraftApiConfigured()) {
        throw new Error('Draft DB URL is not configured in _data/editor.yml.');
      }

      const built = buildPostContent(false);
      const isUpdate = Boolean(state.sourcePostFilename);
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
      markAutosaveBaseline();

      await refreshLibrary(false).catch(function() {
        // no-op
      });
      await fetchAutosaveList(false).catch(function() {
        // no-op
      });

      const blogLink = post.html_url || ('{{ "/blog/" | relative_url }}');
      const verb = isUpdate ? 'Updated' : 'Published';
      setStatus(verb + '. It will appear on /blog/ after GitHub Pages rebuilds. ' + blogLink, 'success');
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
      state.autosaves = [];
      renderAutosaveList();
      setDraftSnapshotLocal(false);
      markAutosaveBaseline();
      if (showMessage) setStatus('Started a new draft.', 'success');
      titleInput.focus();
    }

    let previewTimer = null;
    let autosaveTimer = null;
    let autosaveRemoteTimer = null;
    function schedulePreview() {
      if (!previewEl) return;
      if (previewTimer) window.clearTimeout(previewTimer);
      previewTimer = window.setTimeout(updatePreview, 120);
    }

    function scheduleAutosave() {
      if (autosaveTimer) window.clearTimeout(autosaveTimer);
      autosaveTimer = window.setTimeout(function() {
        setDraftSnapshotLocal(false);
      }, 400);
    }

    async function runRemoteAutosaveIfChanged() {
      if (!state.shellVisible || !hasDraftApiConfigured() || state.autosaveInFlight) return;
      const currentFingerprint = autosaveFingerprint();
      if (currentFingerprint === state.lastAutosaveFingerprint) return;

      state.autosaveInFlight = true;
      try {
        await createAutosaveRemote(false);
      } catch (err) {
        // no-op
      } finally {
        state.autosaveInFlight = false;
      }
    }

    function scheduleRemoteAutosave() {
      if (autosaveRemoteTimer) window.clearTimeout(autosaveRemoteTimer);
      autosaveRemoteTimer = window.setTimeout(function() {
        runRemoteAutosaveIfChanged();
      }, autosaveIntervalMs);
    }

    function onEditorInput() {
      schedulePreview();
      scheduleAutosave();
      scheduleRemoteAutosave();
    }

    function refreshPreviewWhenRenderersReady() {
      if (!previewEl) return;
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
      if (!previewEl) return;
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

    function buildFullPagePreviewHtml() {
      const built = buildPostContent(true);
      const renderedBody = built.body
        ? renderMarkdownToHtml(built.body)
        : '<p class="blog-editor-preview-empty">Start writing markdown on the left.</p>';
      const dateLabel = formatDateLabel(built.date);
      const safeTitle = escapeHtml(built.title || 'Untitled Draft');
      const safeDate = escapeHtml(dateLabel || '');
      const origin = window.location.origin || '';
      const styleHref = origin + '{{ "/assets/css/style.css" | relative_url }}';
      const customHref = origin + '{{ "/static/css/custom.css" | relative_url }}';
      const blogHref = origin + '{{ "/blog/" | relative_url }}';

      return [
        '<!DOCTYPE html>',
        '<html lang="en-US">',
        '<head>',
          '<meta charset="UTF-8">',
          '<meta name="viewport" content="width=device-width, initial-scale=1">',
          '<title>' + safeTitle + ' (Preview)</title>',
          '<link rel="stylesheet" href="' + styleHref + '">',
          '<link rel="stylesheet" href="' + customHref + '">',
        '</head>',
        '<body class="blog-standalone">',
          '<div class="wrapper">',
            '<section>',
              '<article class="post-article">',
                '<p class="post-breadcrumb"><a href="' + blogHref + '">&larr; Back to Blog</a></p>',
                '<h2 class="post-title">' + safeTitle + '</h2>',
                (safeDate ? '<p class="post-date">' + safeDate + '</p>' : ''),
                '<div class="post-content">' + renderedBody + '</div>',
                '<section class="post-comments">',
                  '<h3>Comments</h3>',
                  '<p>Comments are disabled in preview mode.</p>',
                '</section>',
              '</article>',
            '</section>',
          '</div>',
          '<script>',
            'window.MathJax = {',
              'tex: {',
                'inlineMath: [["$", "$"], ["\\\\(", "\\\\)"]],',
                'displayMath: [["$$", "$$"], ["\\\\[", "\\\\]"]],',
                'processEscapes: true',
              '},',
              'options: {',
                'skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"]',
              '}',
            '};',
          '<\/script>',
          '<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"><\/script>',
          '<script>',
            'window.addEventListener("load", function() {',
              'if (window.MathJax && typeof window.MathJax.typesetPromise === "function") {',
                'window.MathJax.typesetPromise();',
              '}',
            '});',
          '<\/script>',
        '</body>',
        '</html>'
      ].join('');
    }

    function openFullPagePreview() {
      try {
        const previewWindow = window.open('about:blank', '_blank');
        if (!previewWindow) {
          setStatus('Popup blocked. Allow popups to open full-page preview.', 'error');
          return false;
        }
        if (typeof previewWindow.focus === 'function') {
          previewWindow.focus();
        }
        const html = buildFullPagePreviewHtml();
        previewWindow.document.open();
        previewWindow.document.write(html);
        previewWindow.document.close();
        if (typeof previewWindow.focus === 'function') {
          previewWindow.focus();
          window.setTimeout(function() {
            try {
              previewWindow.focus();
            } catch (err) {
              // no-op
            }
          }, 0);
        }
        setStatus('Opened full-page preview in a new tab.', 'success');
        return true;
      } catch (err) {
        setStatus(err && err.message ? err.message : 'Unable to open full-page preview.', 'error');
        return false;
      }
    }

    async function copyTextToClipboard(text) {
      if (!text) return false;
      if (!navigator || !navigator.clipboard || typeof navigator.clipboard.writeText !== 'function') {
        return false;
      }
      try {
        await navigator.clipboard.writeText(text);
        return true;
      } catch (err) {
        return false;
      }
    }

    async function createSharedPreviewLink() {
      if (!hasDraftApiConfigured()) {
        setStatus('Share links require Draft DB API configuration.', 'error');
        return false;
      }

      const built = buildPostContent(true);
      const payload = {
        title: built.title,
        date: built.date,
        body: bodyInput.value,
        source_draft_id: state.currentDraftId
      };

      const response = await apiRequest(
        '/api/previews',
        { method: 'POST', body: JSON.stringify(payload) },
        true
      );
      if (response === null) {
        setStatus('Authentication is required to create a share link.', 'error');
        return false;
      }
      if (!response.ok) {
        throw new Error(await parseErrorMessage(response));
      }

      const result = await response.json();
      const previewUrl = result && typeof result.preview_url === 'string'
        ? result.preview_url.trim()
        : '';
      if (!previewUrl) {
        throw new Error('Preview link was not returned by server.');
      }

      const copied = await copyTextToClipboard(previewUrl);
      if (copied) {
        setStatus('Share link copied to clipboard.', 'success');
      } else {
        setStatus('Share link created.', 'success');
      }
      window.prompt('Share this draft preview link', previewUrl);
      return true;
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
      state.shellVisible = true;
      syncLockVisibility();

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
          await fetchAutosaveList(false);
        } catch (err) {
          state.autosaves = [];
          renderAutosaveList();
        }
      } else {
        renderDraftList();
        renderPostList();
        renderAutosaveList();
      }

      updateContextLabel();
      updatePreview();
      markAutosaveBaseline();
      refreshPreviewWhenRenderersReady();
      titleInput.focus();
    }

    function hideShell() {
      setDraftSnapshotLocal(false);
      shell.hidden = true;
      state.shellVisible = false;
      syncLockVisibility();
      setSaveButtonState('idle');
      if (autosaveRemoteTimer) {
        window.clearTimeout(autosaveRemoteTimer);
        autosaveRemoteTimer = null;
      }
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

    function isSaveShortcut(event) {
      const key = (event.key || '').toLowerCase();
      if (key !== 's') return false;
      if (event.altKey) return false;
      return event.metaKey || event.ctrlKey;
    }

    function isPreviewShortcut(event) {
      const key = (event.key || '').toLowerCase();
      if (key !== 'enter') return false;
      if (event.altKey) return false;
      return event.metaKey || event.ctrlKey;
    }

    function isFocusInComposePane() {
      if (!composePane) return false;
      const active = document.activeElement;
      return Boolean(active && composePane.contains(active));
    }

    function handlePreviewShortcut(event) {
      if (!state.shellVisible) return false;
      if (!isPreviewShortcut(event)) return false;
      if (!isFocusInComposePane()) return false;
      event.preventDefault();
      event.stopPropagation();
      if (fullPreviewBtn && typeof fullPreviewBtn.click === 'function') {
        fullPreviewBtn.click();
      } else {
        openFullPagePreview();
      }
      return true;
    }

    async function handleSaveAction() {
      if (saveActionInFlight) return false;
      saveActionInFlight = true;
      setSaveButtonState('saving');

      let didSave = false;
      const localSaved = setDraftSnapshotLocal(false);
      if (!hasDraftApiConfigured()) {
        if (localSaved) {
          setStatus('Saved locally. Configure Draft DB URL for backend saves.', 'success');
          didSave = true;
        } else {
          setStatus('Unable to save draft locally.', 'error');
        }
        setSaveButtonState(didSave ? 'saved' : 'error');
        saveActionInFlight = false;
        return didSave;
      }

      try {
        const remoteSaved = await createAutosaveRemote(true);
        if (remoteSaved) {
          setStatus('Saved version to database.', 'success');
          didSave = true;
          return true;
        }
        if (localSaved) {
          setStatus('Saved locally. Authentication is required for backend save.', 'error');
          didSave = true;
        } else {
          setStatus('Unable to save draft.', 'error');
        }
      } catch (err) {
        if (localSaved) {
          setStatus('Saved locally. Database save failed: ' + (err.message || 'unknown error') + '.', 'error');
          didSave = true;
        } else {
          setStatus(err && err.message ? err.message : 'Unable to save draft.', 'error');
        }
      } finally {
        setSaveButtonState(didSave ? 'saved' : 'error');
        saveActionInFlight = false;
      }

      return didSave;
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
        const deleteTarget = event.target && event.target.closest('[data-delete-draft-id]');
        if (deleteTarget) {
          const deleteId = (deleteTarget.getAttribute('data-delete-draft-id') || '').trim();
          if (!deleteId) return;
          const selectedDraft = state.drafts.find(function(item) {
            return item && item.draft_id === deleteId;
          });
          const label = selectedDraft && selectedDraft.title ? selectedDraft.title : deleteId;
          const confirmed = window.confirm('Delete draft "' + label + '" and all its saves?');
          if (!confirmed) return;

          try {
            const deleted = await deleteDraftRemote(deleteId, true);
            if (!deleted) {
              setStatus('Draft not found.', 'error');
              return;
            }
            const deletedCurrent = deleteId === state.currentDraftId;
            if (deletedCurrent) {
              startNewDraft(false);
            }
            if (hasDraftApiConfigured()) {
              await fetchDraftList(false).catch(function() {
                // no-op
              });
            }
            if (deletedCurrent) {
              state.autosaves = [];
              renderAutosaveList();
            }
            setStatus('Draft deleted.', 'success');
          } catch (err) {
            setStatus(err && err.message ? err.message : 'Unable to delete draft.', 'error');
          }
          return;
        }

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

    if (autosaveListEl) {
      autosaveListEl.addEventListener('click', async function(event) {
        const target = event.target && event.target.closest('[data-autosave-id]');
        if (!target) return;
        const autosaveId = (target.getAttribute('data-autosave-id') || '').trim();
        if (!autosaveId) return;
        try {
          const loaded = await loadAutosaveById(autosaveId, true, true);
          if (!loaded) {
            setStatus('Autosave not found.', 'error');
          }
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to load autosave.', 'error');
        }
      });
    }

    if (postListEl) {
      postListEl.addEventListener('click', async function(event) {
        const deleteTarget = event.target && event.target.closest('[data-delete-post-filename]');
        if (deleteTarget) {
          const filenameToDelete = (deleteTarget.getAttribute('data-delete-post-filename') || '').trim();
          if (!filenameToDelete) return;
          const selectedPost = state.posts.find(function(item) {
            return item && item.filename === filenameToDelete;
          });
          const label = selectedPost && selectedPost.title ? selectedPost.title : filenameToDelete;
          const confirmed = window.confirm('Delete published post "' + label + '"? This removes it from /blog/.');
          if (!confirmed) return;
          try {
            const deleted = await deletePublishedPostRemote(filenameToDelete, true);
            if (!deleted) {
              setStatus('Published post not found.', 'error');
              return;
            }
            setStatus('Published post deleted.', 'success');
          } catch (err) {
            setStatus(err && err.message ? err.message : 'Unable to delete published post.', 'error');
          }
          return;
        }

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
        await handleSaveAction();
      });
    }

    if (fullPreviewBtn) {
      fullPreviewBtn.addEventListener('click', function() {
        openFullPagePreview();
      });
    }

    if (sharePreviewBtn) {
      sharePreviewBtn.addEventListener('click', async function() {
        try {
          await createSharedPreviewLink();
        } catch (err) {
          setStatus(err && err.message ? err.message : 'Unable to create share link.', 'error');
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
      if (handlePreviewShortcut(event)) {
        return;
      }
      if (state.shellVisible && isSaveShortcut(event) && isFocusInComposePane()) {
        event.preventDefault();
        handleSaveAction();
        return;
      }
      if (isComposeShortcut(event)) {
        event.preventDefault();
        requestUnlockAndShow({ allowPrompt: true, silent: false });
      }
    });

    if (composePane) {
      composePane.addEventListener('keydown', function(event) {
        handlePreviewShortcut(event);
      }, true);
    }

    window.addEventListener('hashchange', maybeRevealFromHash);
    window.addEventListener('beforeunload', function() {
      if (state.shellVisible) setDraftSnapshotLocal(false);
    });

    hideShell();
    applySidebarCollapsed(false);
    maybeRevealFromHash();
    maybeAutoUnlockFromStoredCredentials().catch(function() {
      // no-op
    });
  })();
</script>
{% endif %}
