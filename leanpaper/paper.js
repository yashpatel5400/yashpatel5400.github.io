const DEFAULT_PAPER_PATH = 'core.tex';
const DEFAULT_BIB_PATH = 'refs.bib';
const PAPERS = [
  {
    id: 'cpo',
    title: 'Conformal Contextual Robust Optimization',
    paper: 'core.tex',
    bib: 'refs.bib'
  }
];
const LATEX_ASSET_BASE = 'https://cdn.jsdelivr.net/npm/latex.js@0.12.6/dist/';

let latexAssetsAttached = false;
let currentPaperId = null;
let equationNumbers = {};
const PROOF_SOURCES = {
  'lemma:coverage_bound': {
    path: 'subopt.lean',
    anchor: 'theorem coverage_bound'
  },
  'lemma:cpo_convergence': {
    path: 'convergence.lean',
    anchor: 'theorem pgd_convergence'
  }
};

document.addEventListener('DOMContentLoaded', () => {
  const initial = resolveInitialPaper();
  renderPaperList(initial.id);
  loadPaper(initial);
});

async function loadPaper(selection) {
  const statusEl = document.getElementById('paper-status');
  const paperEl = document.getElementById('paper-content');
  const { paperPath, bibPath, title, id } = selection || resolveInitialPaper();
  currentPaperId = id || null;
  renderPaperList(currentPaperId);

  setStatus(statusEl, 'Loading main paper…');

  const bibPromise = bibPath
    ? fetchBibliography(bibPath).catch(err => {
        console.warn('Failed to load bibliography', err);
        return null;
      })
    : Promise.resolve(null);

  try {
    const res = await fetch(paperPath);
    if (!res.ok) {
      throw new Error(`Request failed with status ${res.status}`);
    }

    const rawTex = await res.text();
    const body = extractBody(rawTex);
    const meta = extractTitleAuthor(body);
    equationNumbers = enumerateEquations(body);
    const citationOrder = collectCitations(body);
    const citationMap = makeCitationMap(citationOrder);
    const bibEntriesAll = (await bibPromise) || [];
    const bibEntries = filterBibliography(bibEntriesAll, citationOrder);
    const forceLatex = new URLSearchParams(window.location.search).get('renderer') === 'latexjs';

    resetPanels();
    updatePaperSubtitle(meta.title || title || paperPath);

    let rendered = false;

    if (!forceLatex) {
      try {
        const html = renderWithMarkdown(body, citationMap, meta, equationNumbers);
        paperEl.innerHTML = html;
        rendered = true;
      } catch (mdErr) {
        console.warn('Markdown render failed, trying LaTeX.js', mdErr);
      }
    }

    if (!rendered) {
      const fragment = renderWithLatexJs(body, citationMap, meta, equationNumbers);
      paperEl.replaceChildren(fragment);
    }

    if (window.MathJax && window.MathJax.typesetPromise) {
      await window.MathJax.typesetPromise([paperEl]);
    }

    if (bibEntries && bibEntries.length) {
      const refsHtml = renderBibliographySection(bibEntries);
      paperEl.insertAdjacentHTML('beforeend', refsHtml);
    }

    attachCitationHandlers(bibEntries);
    attachLemmaHandlers();
    setStatus(statusEl, '');
  } catch (err) {
    console.error(err);
    setStatus(statusEl, 'Failed to load paper');
    paperEl.innerHTML = `<div class="error">Could not load paper: ${err.message}</div>`;
  }
}

function setStatus(el, text) {
  if (el) {
    el.textContent = text;
  }
}

function extractBody(tex) {
  const start = tex.indexOf('\\begin{document}');
  const end = tex.indexOf('\\end{document}');

  if (start !== -1 && end !== -1 && end > start) {
    return tex.slice(start + '\\begin{document}'.length, end).trim();
  }

  return tex;
}

function renderWithLatexJs(body, citationMap, meta, eqNumbers) {
  if (!window.latexjs) {
    throw new Error('LaTeX.js is not available on window.latexjs');
  }

  const normalized = normalizeLatex(body, citationMap, meta, eqNumbers);
  const generator = new window.latexjs.HtmlGenerator({ hyphenate: false });

  window.latexjs.parse(normalized, { generator });

  attachLatexAssets(generator);

  return generator.domFragment();
}

function attachLatexAssets(generator) {
  if (latexAssetsAttached) return;
  const assets = generator.stylesAndScripts(LATEX_ASSET_BASE);
  document.head.appendChild(assets);
  latexAssetsAttached = true;
}

function normalizeLatex(body, citationMap, meta, eqNumbers) {
  const macroPrelude = [
    '\\newcommand{\\aistatstitle}[1]{\\section*{#1}}',
    '\\newcommand{\\aistatsauthor}[1]{}',
    '\\newcommand{\\aistatsaddress}[1]{}',
    '\\newcommand{\\textproc}[1]{\\texttt{#1}}',
    '\\newcommand{\\mathds}[1]{\\mathbb{#1}}',
    '\\newcommand{\\citep}[1]{[ #1 ]}',
    '\\newcommand{\\citet}[1]{[ #1 ]}',
    '\\newcommand{\\argmax}{\\mathrm{argmax}}',
    '\\newcommand{\\argmin}{\\mathrm{argmin}}',
    '\\newcommand{\\logit}{\\mathrm{logit}}',
    '\\newcommand{\\ceil}[1]{\\lceil #1 \\rceil}',
    '\\newcommand{\\floor}[1]{\\lfloor #1 \\rfloor}'
  ].join('\n');

  let text = body.replace(/^%.*$/gm, '');
  text = text.replace(/\\twocolumn\[/g, '');
  text = text.replace(/^\]\s*$/gm, '');
  text = text.replace(/\\usepackage[^\n]*\n/g, '');
  text = text.replace(/\\bibliographystyle\{[^}]*\}/g, '');
  text = text.replace(/\\addbibresource\{[^}]*\}/g, '');
  text = text.replace(/\\newpage/g, '');
  text = text.replace(/\\onecolumn/g, '');
  text = text.replace(/\\appendix/g, '\\section*{Appendix}');
  text = normalizeQuotes(text);
  text = stripLeadingIndent(text);
  text = injectLabelAnchors(text);
  text = wrapLemmaProof(text);
  text = applyTitleAuthor(text, meta, 'latex');
  text = convertTextStyles(text, 'latex');
  text = convertLists(text, 'latex');

  text = linkCitations(text, citationMap, (num, slug, key) => `<a class="citation" data-citekey="${key}" href="#ref-${slug}">[${num}]</a>`);
  text = linkCrossReferences(text, equationNumbers);

  // Normalize theorem-like environments into plain paragraphs so LaTeX.js can render without style files.
  const theoremish = [
    ['theorem', 'Theorem.'],
    ['lemma', 'Lemma.'],
    ['assumption', 'Assumption.'],
    ['corollary', 'Corollary.'],
    ['conjecture', 'Conjecture.'],
    ['proof', 'Proof.']
  ];

  theoremish.forEach(([env, label]) => {
    const beginPattern = new RegExp(`\\\\begin\\{${env}\\*?\\}`, 'g');
    const endPattern = new RegExp(`\\\\end\\{${env}\\*?\\}`, 'g');
    text = text.replace(beginPattern, `\\\\paragraph{${label}}`);
    text = text.replace(endPattern, '');
  });

  // LaTeX.js path: drop figures to simple captions to avoid invalid HTML in the parser.
  text = text.replace(/\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}/g, fig => {
    const caption = (fig.match(/\\caption\{([^}]*)\}/) || [])[1];
    return caption ? `\\begin{quote}${caption}\\end{quote}` : '';
  });
  text = text.replace(/\\includegraphics\[.*?\]\{[^}]*\}/g, '');

  text = replaceAlgorithms(text, 'latex');

  return `${macroPrelude}\n${text}`;
}

function renderWithMarkdown(body, citationMap, meta, eqNumbers) {
  if (!window.marked) {
    throw new Error('marked is not available for rendering');
  }

  const withAnchors = injectLabelAnchors(body);
  const withCrossRefs = linkCrossReferences(withAnchors);
  const linkedBody = linkCitations(withCrossRefs, citationMap, (num, slug, key) => `<a class="citation" data-citekey="${key}" href="#ref-${slug}">[${num}]</a>`);
  const mdSource = latexToMarkdown(linkedBody, meta, eqNumbers);
  const { text, placeholders } = extractMathPlaceholders(mdSource);
  window.marked.setOptions({
    mangle: false,
    headerIds: false
  });

  const html = window.marked.parse(text);
  return restoreMathPlaceholders(html, placeholders);
}

function latexToMarkdown(body, meta, eqNumbers) {
  let md = normalizeQuotes(body.replace(/^%.*$/gm, ''));
  md = applyTitleAuthor(md, meta, 'markdown');

  md = md.replace(/\\twocolumn\[/g, '');
  md = md.replace(/^\]\s*$/gm, '');
  md = md.replace(/\\aistatstitle\{([^}]*)\}/, '# $1\n');
  md = md.replace(/\\aistatsauthor\{([^}]*)\}/, '*$1*\n');
  md = md.replace(/\\aistatsaddress\{([^}]*)\}/, '*$1*\n');

  md = md.replace(/\\begin\{abstract\}/, '### Abstract\n');
  md = md.replace(/\\end\{abstract\}/, '\n');

  md = md.replace(/\\section\{([^}]*)\}/g, '## $1');
  md = md.replace(/\\subsection\{([^}]*)\}/g, '### $1');
  md = md.replace(/\\subsubsection\{([^}]*)\}/g, '#### $1');

  md = stripLeadingIndent(md);
  md = convertEquations(md, eqNumbers);
  md = injectLabelAnchors(md);
  md = wrapLemmaProof(md);
  md = md.replace(/\\textproc\{([^}]*)\}/g, '`$1`');
  md = md.replace(/\\mathds\{([^}]*)\}/g, (_, symbol) => `\\mathbb{${symbol}}`);
  md = md.replace(/\\cite(p|t)?\{([^}]*)\}/g, '[$2]');
  md = convertTextStyles(md, 'markdown');

  md = replaceAlgorithms(md, 'markdown');

  md = convertLists(md, 'markdown');
  md = convertFigures(md, 'markdown');
  md = convertStandaloneGraphics(md, 'markdown');

  const envToHeading = {
    lemma: 'Lemma.',
    theorem: 'Theorem.',
    corollary: 'Corollary.',
    conjecture: 'Conjecture.',
    assumption: 'Assumption.',
    proof: 'Proof.'
  };

  Object.entries(envToHeading).forEach(([env, heading]) => {
    const beginPattern = new RegExp(`\\\\begin\\{${env}\\*?\\}`, 'g');
    const endPattern = new RegExp(`\\\\end\\{${env}\\*?\\}`, 'g');
    md = md.replace(beginPattern, `**${heading}**`);
    md = md.replace(endPattern, '');
  });

  md = md.replace(/\\appendix/g, '\n## Appendix\n');
  md = md.replace(/\\newpage/g, '');
  md = md.replace(/\\onecolumn/g, '');
  md = md.replace(/\\twocolumn/g, '');

  md = md.replace(/\n{3,}/g, '\n\n');

  return md.trim();
}

function extractMathPlaceholders(mdSource) {
  const placeholders = [];
  let text = mdSource;

  const patterns = [
    /\$\$[\s\S]*?\$\$/g,      // display math with $$
    /\\\[[\s\S]*?\\\]/g,      // display math with \[ \]
    /\$[^$\n]*\$/g            // inline math $
  ];

  patterns.forEach(pattern => {
    text = text.replace(pattern, match => {
      const key = `@@MATH${placeholders.length}@@`;
      placeholders.push(match);
      return key;
    });
  });

  return { text, placeholders };
}

function restoreMathPlaceholders(html, placeholders) {
  return placeholders.reduce((acc, math, idx) => acc.replace(`@@MATH${idx}@@`, math), html);
}

function resolveInitialPaper() {
  const { paperPath, bibPath } = getAssetPaths();
  const matched = PAPERS.find(p => p.paper === paperPath) || null;
  if (matched) {
    return { id: matched.id, title: matched.title, paperPath: matched.paper, bibPath: matched.bib };
  }
  return { id: null, title: paperPath, paperPath, bibPath };
}

function collectCitations(text) {
  const citeRegex = /\\cite(p|t)?\{([^}]*)\}/g;
  const order = [];
  const seen = new Set();
  let match;

  while ((match = citeRegex.exec(text)) !== null) {
    const keys = match[2].split(',').map(k => k.trim()).filter(Boolean);
    keys.forEach(key => {
      if (!seen.has(key)) {
        seen.add(key);
        order.push(key);
      }
    });
  }

  return order;
}

function makeCitationMap(order) {
  const map = {};
  order.forEach((key, idx) => {
    map[key] = idx + 1;
  });
  return map;
}

function filterBibliography(entries, citationOrder) {
  if (!entries || !entries.length) return [];
  const byKey = new Map(entries.map(e => [e.citekey, e]));
  return citationOrder
    .map((key, idx) => {
      const entry = byKey.get(key);
      if (!entry) return { citekey: key, fields: { title: key }, number: idx + 1 };
      return { ...entry, number: idx + 1 };
    })
    .filter(Boolean);
}

function getAssetPaths() {
  const params = new URLSearchParams(window.location.search);
  const paperPath = params.get('paper') || DEFAULT_PAPER_PATH;
  const bibPath = params.get('bib') || DEFAULT_BIB_PATH;
  return { paperPath, bibPath };
}

async function fetchBibliography(path) {
  const res = await fetch(path);
  if (!res.ok) {
    throw new Error(`References not found (${res.status})`);
  }

  const raw = await res.text();
  return parseBibtex(raw);
}

function parseBibtex(raw) {
  const entries = [];
  const cleaned = raw.replace(/^[ \t]*%.*$/gm, '');
  const entryRegex = /@(\w+)\s*\{\s*([^,]+),([\s\S]*?)\n\}/g;
  let match;

  while ((match = entryRegex.exec(cleaned)) !== null) {
    const [, type, citekey, body] = match;
    const fields = {};
    const fieldRegex = /(\w+)\s*=\s*(\{[^{}]*\}|\"[^\"]*\"|[^,\n]+)\s*,?/g;
    let fieldMatch;
    while ((fieldMatch = fieldRegex.exec(body)) !== null) {
      const [, key, rawVal] = fieldMatch;
      const val = rawVal
        .trim()
        .replace(/^{|}$/g, '')
        .replace(/^\"|\"$/g, '')
        .replace(/\s+/g, ' ');
      fields[key.toLowerCase()] = val;
    }

    entries.push({ type: type.toLowerCase(), citekey, fields });
  }

  return entries;
}

function renderBibliographySection(entries) {
  const items = entries
    .map(entry => {
      const slug = slugifyCiteKey(entry.citekey);
      const label = entry.number || '';
      return `<li id="ref-${slug}"><span class="ref-label">[${label}]</span> ${formatBibEntry(entry)}</li>`;
    })
    .join('');

  return `
    <section class="references">
      <h2 id="references">References</h2>
      <ol>
        ${items}
      </ol>
    </section>
  `;
}

function formatBibEntry({ citekey, fields }) {
  const title = fields.title || citekey;
  const authors = fields.author ? formatAuthors(fields.author) : '';
  const venue = fields.journal || fields.booktitle || '';
  const year = fields.year ? ` (${fields.year})` : '';
  const link = fields.doi
    ? ` <a href="https://doi.org/${fields.doi}" target="_blank" rel="noopener noreferrer">doi</a>`
    : fields.url
    ? ` <a href="${fields.url}" target="_blank" rel="noopener noreferrer">link</a>`
    : '';

  const parts = [
    `<span class="ref-title">${title}</span>${year}`,
    authors && ` ${authors}`,
    venue && ` — ${venue}`,
    link
  ].filter(Boolean);

  return parts.join('');
}

function formatAuthors(raw) {
  const authors = raw.split(/\s+and\s+/i).map(a => a.trim());
  if (authors.length === 1) return authors[0];
  if (authors.length === 2) return `${authors[0]} & ${authors[1]}`;
  return `${authors.slice(0, -1).join(', ')}, & ${authors[authors.length - 1]}`;
}

function linkCitations(text, citationMap, formatter) {
  if (!citationMap || Object.keys(citationMap).length === 0) return text;
  const citeRegex = /\\cite(p|t)?\{([^}]*)\}/g;
  return text.replace(citeRegex, (_, __, content) => {
    const keys = content.split(',').map(k => k.trim()).filter(Boolean);
    if (!keys.length) return '';
    const links = keys.map(key => {
      const num = citationMap[key];
      if (!num) return key;
      return formatter(num, slugifyCiteKey(key), key);
    });
    return links.join(' ');
  });
}

function slugifyCiteKey(key) {
  return key.toLowerCase().replace(/[^a-z0-9_-]+/g, '-');
}

function attachCitationHandlers(entries) {
  const paperEl = document.getElementById('paper-content');
  const sidePanel = document.getElementById('side-panel-body');
  if (!paperEl || !sidePanel) return;
  const byKey = new Map(entries.map(e => [e.citekey, e]));

  paperEl.querySelectorAll('a.citation').forEach(anchor => {
    anchor.addEventListener('click', evt => {
      evt.preventDefault();
      const key = anchor.dataset.citekey;
      const entry = byKey.get(key);
      if (entry) {
        sidePanel.innerHTML = renderReferenceDetail(entry);
        sidePanel.className = 'reference-detail';
      } else {
        sidePanel.innerHTML = `<p>Reference not found for ${key}.</p>`;
        sidePanel.className = 'proof-placeholder';
      }
    });
  });
}

function attachLemmaHandlers() {
  const paperEl = document.getElementById('paper-content');
  const sidePanel = document.getElementById('side-panel-body');
  if (!paperEl || !sidePanel) return;

  paperEl.querySelectorAll('.lemma-block').forEach(block => {
    const label = block.dataset.label;
    if (!label) return;
    block.style.cursor = 'pointer';
    block.addEventListener('click', async () => {
      sidePanel.className = 'reference-detail';
      sidePanel.innerHTML = '<p class="muted">Loading Lean proof…</p>';
      try {
        const proofHtml = await loadLeanProof(label);
        sidePanel.innerHTML = proofHtml;
      } catch (err) {
        sidePanel.innerHTML = `<p>Could not load Lean proof for ${label}: ${err.message}</p>`;
        sidePanel.className = 'proof-placeholder';
      }
    });
  });
}

async function loadLeanProof(label) {
  const source = PROOF_SOURCES[label];
  if (!source) {
    throw new Error('No proof source configured for this label');
  }

  const res = await fetch(source.path);
  if (!res.ok) {
    throw new Error(`Failed to fetch ${source.path} (${res.status})`);
  }
  const text = await res.text();
  const snippet = extractLeanSnippet(text, source.anchor);

  return `
    <div class="reference-detail">
      <div class="env-heading">${formatRefLabel(label)}</div>
      <pre><code class="lean">${escapeHtml(snippet)}</code></pre>
    </div>
  `;
}

function extractLeanSnippet(fileText, anchor) {
  if (!anchor) return fileText;
  const idx = fileText.indexOf(anchor);
  if (idx === -1) return fileText;
  const tail = fileText.slice(idx);
  const lines = tail.split('\n');
  const collected = [];
  for (const line of lines) {
    if (/^theorem\s+/i.test(line) && collected.length > 0) break;
    collected.push(line);
    // stop if line contains "by" with proof term and next line blank
    if (/^end\b/.test(line.trim())) break;
  }
  return collected.join('\n').trim();
}

function renderReferenceDetail(entry) {
  const title = entry.fields.title || entry.citekey;
  const authors = entry.fields.author ? formatAuthors(entry.fields.author) : '';
  const venue = entry.fields.journal || entry.fields.booktitle || '';
  const year = entry.fields.year || '';
  const url = entry.fields.url || '';
  const doiUrl = entry.fields.doi ? `https://doi.org/${entry.fields.doi}` : '';
  const primaryLink = url || doiUrl;
  const searchLink = `https://scholar.google.com/scholar?q=${encodeURIComponent(title)}`;

  const parts = [
    `<span class="ref-title">${title}${year ? ` (${year})` : ''}</span>`,
    authors ? `<div class="ref-authors">${authors}</div>` : '',
    venue ? `<div class="ref-venue">${venue}</div>` : '',
    primaryLink
      ? `<div><a href="${primaryLink}" target="_blank" rel="noopener noreferrer">View source</a></div>`
      : `<div><a href="${searchLink}" target="_blank" rel="noopener noreferrer">Google Scholar</a></div>`,
    url && doiUrl && url !== doiUrl
      ? `<div><a href="${doiUrl}" target="_blank" rel="noopener noreferrer">DOI</a></div>`
      : ''
  ].filter(Boolean);

  return parts.join('');
}

function injectLabelAnchors(text) {
  return text.replace(/\\label\{([^}]*)\}/g, (_, label) => `<span id="cref-${label}"></span>`);
}

function linkCrossReferences(text, eqNumbers = {}) {
  const refRegex = /\\[cC]ref\{([^}]*)\}/g;
  return text.replace(refRegex, (_, content) => {
    const labels = content.split(',').map(l => l.trim()).filter(Boolean);
    if (!labels.length) return '';
    const links = labels.map(label => {
      const text = formatRefLabel(label, eqNumbers);
      return `<a class="cross-ref" href="#cref-${label}">${text}</a>`;
    });
    return links.join(' ');
  });
}

function formatRefLabel(label, eqNumbers = {}) {
  if (eqNumbers[label]) {
    const parts = label.split(':');
    const remainder = parts.slice(1).join(':');
    const name = humanizeLabel(remainder);
    return `Equation ${eqNumbers[label]}${name ? `: ${name}` : ''}`;
  }

  const parts = label.split(':');
  const prefix = parts[0] || '';
  const remainder = parts.slice(1).join(':');

  if (prefix === 'lemma') {
    return `Lemma: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'eqn') {
    return `Equation: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'alg' || prefix === 'algorithm') {
    return `Algorithm: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'theorem') {
    return `Theorem: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'assumption') {
    return `Assumption: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'corollary') {
    return `Corollary: ${humanizeLabel(remainder)}`;
  }
  if (prefix === 'conjecture') {
    return `Conjecture: ${humanizeLabel(remainder)}`;
  }

  return `[${label}]`;
}

function humanizeLabel(text) {
  if (!text) return '';
  const special = {
    pgd: 'PGD',
    cpo: 'CPO'
  };
  return text
    .split(/[_\-]+/)
    .filter(Boolean)
    .map(word => {
      const lower = word.toLowerCase();
      if (special[lower]) return special[lower];
      return word.charAt(0).toUpperCase() + word.slice(1);
    })
    .join(' ');
}

function formatEnvHeading(kind, labelId) {
  const parts = labelId.split(':');
  const maybeName = parts.slice(1).join(':') || parts[0];
  const nice = humanizeLabel(maybeName);
  return `${kind}: ${nice}`;
}

function normalizeQuotes(text) {
  // Convert LaTeX-style opening quotes ``text'' to standard typographic quotes.
  return text.replace(/``([^`]+)''/g, '“$1”');
}

function convertFigures(text, mode) {
  const figRegex = /\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}/g;
  return text.replace(figRegex, fig => {
    const caption = (fig.match(/\\caption\{([\s\S]*?)\}/) || [])[1] || '';
    const graphics = fig.match(/\\includegraphics(?:\[(.*?)\])?\{([^}]*)\}/);
    const options = graphics ? graphics[1] : '';
    const src = graphics ? resolveImagePath(graphics[2]) : '';
    const style = options ? graphicsOptionsToStyle(options) : '';
    const anchor = (fig.match(/<span id="[^"]*"><\/span>/) || [])[0] || '';

    if (!src) {
      const textContent = caption || 'Figure';
      return mode === 'markdown' ? `${anchor}> ${textContent}\n` : `${anchor}\\begin{quote}${textContent}\\end{quote}`;
    }

    const figureHtml = `<figure class="figure-block"><img src="${src}" alt="${caption || 'Figure'}"${style ? ` style="${style}"` : ''}>${caption ? `<figcaption>${caption}</figcaption>` : ''}</figure>`;
    return mode === 'markdown' ? `\n${anchor}${figureHtml}\n` : `${anchor}${figureHtml}`;
  });
}

function convertStandaloneGraphics(text, mode) {
  const imgRegex = /\\includegraphics(?:\[(.*?)\])?\{([^}]*)\}/g;
  return text.replace(imgRegex, (_, options = '', src = '') => {
    const style = options ? graphicsOptionsToStyle(options) : '';
    const resolved = resolveImagePath(src);
    if (!resolved) return '';
    const alt = '';
    const tag = `<img class="inline-graphic" src="${resolved}" alt="${alt}"${style ? ` style="${style}"` : ''}>`;
    return tag;
  });
}

function graphicsOptionsToStyle(options) {
  // Basic handling for scale or width options.
  const scaleMatch = options.match(/scale\s*=\s*([0-9.]+)/);
  if (scaleMatch) {
    const pct = Math.round(parseFloat(scaleMatch[1]) * 100);
    if (!Number.isNaN(pct)) {
      return `max-width: ${pct}%`;
    }
  }
  const widthMatch = options.match(/width\s*=\s*([0-9.]+)\s*\\?textwidth/);
  if (widthMatch) {
    const pct = Math.round(parseFloat(widthMatch[1]) * 100);
    if (!Number.isNaN(pct)) {
      return `max-width: ${pct}%`;
    }
  }
  return '';
}

function resolveImagePath(src) {
  if (!src) return '';
  // If already absolute or has a slash, leave it; otherwise, try images/ as a fallback.
  if (/^(https?:)?\/\//.test(src) || src.includes('/')) return src;
  return `images/${src}`;
}

function convertEquations(text, eqNumbers = {}) {
  const clean = expr =>
    expr
      .trim()
      .replace(/^\$\$/g, '')
      .replace(/\$\$$/g, '')
      .replace(/^\\\[/g, '')
      .replace(/\\\]$/g, '');

  const wrap = (inner, label) => {
    const idAttr = label ? ` id="cref-${label}"` : '';
    const num = label && eqNumbers[label] ? eqNumbers[label] : null;
    const numberHtml = num ? `<span class="eq-number">(${num})</span>` : '';
    return `\n<div class="equation-block"${idAttr}>$$\n${clean(inner)}\n$$${numberHtml}</div>\n`;
  };
  const replaceBlock = (_match, body) => wrap(body);
  const replaceAlign = (_match, body) => wrap(body);

  return text
    .replace(/[ \t]*\\begin\{equation\*?\}([\s\S]*?)\\end\{equation\*?\}[ \t]*/g, (m, body) => {
      const { cleaned, label } = stripLabel(body);
      return wrap(cleaned, label);
    })
    .replace(/[ \t]*\\begin\{gather\*?\}([\s\S]*?)\\end\{gather\*?\}[ \t]*/g, (m, body) => {
      const { cleaned, label } = stripLabel(body);
      return wrap(cleaned, label);
    })
    .replace(/[ \t]*\\begin\{align\*?\}([\s\S]*?)\\end\{align\*?\}[ \t]*/g, (m, body) => {
      const { cleaned, label } = stripLabel(body);
      return wrap(cleaned, label);
    });
}

function stripLeadingIndent(text) {
  return text.replace(/^[ \t]+/gm, '');
}

function replaceAlgorithms(text, mode) {
  return text.replace(/\\begin\{algorithm\}[\s\S]*?\\end\{algorithm\}/g, block => {
    const captionRaw = (block.match(/\\caption\{([\s\S]*?)\}/) || [])[1] || '';
    const caption = captionRaw.replace(/\\label\{[^}]*\}/, '').replace(/[`]/g, '').trim();
    const label = (block.match(/\\label\{([^}]*)\}/) || [])[1] || '';
    const body = block
      .replace(/\\begin\{algorithmic\}\[?\d*\]?/g, '')
      .replace(/\\end\{algorithmic\}/g, '')
      .replace(/\\caption\{[^}]*\}/g, '')
      .replace(/\\label\{[^}]*\}/g, '');

    const steps = parseAlgorithmLines(body);

    if (!steps.length && !caption) return '';

    const items = steps.map(step => `<li>${step}</li>`).join('');
    const title = caption ? `Algorithm: ${caption}` : 'Algorithm';
    return `<div class="algorithm-block"${label ? ` id="cref-${label}"` : ''}>${caption ? `<div class="algo-caption">${title}</div>` : ''}<ol>${items}</ol></div>`;
  });
}

function convertLists(text, mode) {
  const replacer = (_match, body) => {
    const items = body
      .split(/\\item/)
      .map(s => s.trim())
      .filter(Boolean)
      .map(item => {
        const styled = convertTextStyles(item, mode === 'markdown' ? 'markdown' : 'latex');
        return `<li>${styled}</li>`;
      })
      .join('');

    const list = `<ul>${items}</ul>`;
    return mode === 'markdown' ? `\n${list}\n` : list;
  };

  return text
    .replace(/\\begin\{itemize\}([\s\S]*?)\\end\{itemize\}/g, replacer)
    .replace(/\\begin\{enumerate\}([\s\S]*?)\\end\{enumerate\}/g, replacer);
}

function parseAlgorithmLines(body) {
  const lines = body
    .split('\n')
    .map(line => line.trim())
    .filter(Boolean)
    .filter(line => {
      const normalized = line.replace(/[^a-zA-Z]/g, '').toLowerCase();
      return normalized !== 'algorithm';
    });

  let forDepth = 0;
  const output = [];

  lines.forEach(line => {
    const lower = line.toLowerCase();
    if (lower === 'algorithm') return;
    const isEndFor = /^\\endfor\b/.test(lower) || /^\\end\{?for\}?/.test(lower);
    if (isEndFor) {
      forDepth = Math.max(0, forDepth - 1);
      return;
    }

    const isFor = /^\\for\b/.test(lower);
    const parsed = transformAlgorithmLine(line);
    if (!parsed) return;

    const styled = applyMarkdownStyleMarkers(convertTextStyles(parsed, 'latex'));
    const maybeIndented = !isFor && forDepth > 0 ? `<span class="algo-indent">${styled}</span>` : styled;
    output.push(maybeIndented);

    if (isFor) {
      forDepth += 1;
    }
  });

  return output.filter(step => {
    const plain = step.replace(/<[^>]*>/g, '').replace(/&nbsp;/g, '').trim().toLowerCase();
    return plain && plain !== 'algorithm';
  });
}

function transformAlgorithmLine(line) {
  const cmdMatch = line.match(/^\\([A-Za-z]+)\s*(\{([^}]*)\})?(.*)/);
  if (cmdMatch) {
    const cmd = cmdMatch[1];
    const braceContent = cmdMatch[3] ? cmdMatch[3].trim() : '';
    const rest = cmdMatch[4].trim();
    if (cmd.toLowerCase() === 'procedure') {
      return '';
    }
    const content = braceContent || rest;
    const cmdLower = cmd.toLowerCase();
    if (cmdLower === 'textbf') {
      return `<strong>${content}</strong>`;
    }
    if (cmdLower === 'procedure') {
      return `<strong>${braceContent || content}</strong>${rest ? ` ${rest}` : ''}`;
    }
    if (cmdLower.startsWith('end')) {
      return '';
    }
    if (cmdLower === 'for') {
      return `For ${content}${rest ? ` ${rest}` : ''}`;
    }
    if (cmdLower === 'statex') {
      return content || rest;
    }
    return content || rest;
  }
  return line;
}

function convertTextStyles(text, mode) {
  if (mode === 'markdown') {
    return text
      .replace(/\\textbf\{([^}]*)\}/g, '**$1**')
      .replace(/\\textit\{([^}]*)\}/g, '*$1*');
  }
  // For LaTeX.js path, translate to HTML so styles survive stripping of packages.
  return text
    .replace(/\\textbf\{([^}]*)\}/g, '<strong>$1</strong>')
    .replace(/\\textit\{([^}]*)\}/g, '<em>$1</em>');
}

function applyMarkdownStyleMarkers(text) {
  return text
    .replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>')
    .replace(/\*([^*]+)\*/g, '<em>$1</em>');
}

function wrapLemmaProof(text) {
  const wrapEnv = (env, title, className) => {
    const regex = new RegExp(`\\\\begin\\{${env}\\}([\\s\\S]*?)\\\\end\\{${env}\\}`, 'g');
    return txt =>
      txt.replace(regex, (_m, body) => {
        let inner = body.trim();
        const labelMatch = inner.match(/<span id="cref-([^"]+)"><\/span>/);
        const labelId = labelMatch ? labelMatch[1] : null;
        if (labelId) {
          inner = inner.replace(/<span id="cref-[^"]+"><\/span>/g, '');
        }
        const headingText = labelId
          ? formatEnvHeading(title.replace('.', ''), labelId)
          : title;
        const anchor = labelId ? `<span id="cref-${labelId}"></span>` : '';
        const heading = `<div class="env-heading">${headingText}</div>`;
        const content = `<div class="env-body">${inner}</div>`;
        const data = labelId ? ` data-label="${labelId}"` : '';
        return `${anchor}<div class="${className}"${data}>${heading}${content}</div>`;
      });
  };

  let out = text;
  out = wrapEnv('lemma', 'Lemma.', 'lemma-block')(out);
  out = wrapEnv('proof', 'Proof.', 'proof-block')(out);
  return out;
}

function stripLabel(body) {
  const match = body.match(/\\label\{([^}]*)\}/);
  if (!match) return { cleaned: body, label: null };
  const cleaned = body.replace(/\\label\{[^}]*\}/, '').trim();
  return { cleaned, label: match[1] };
}

function enumerateEquations(text) {
  const regex = /\\begin\{(?:equation\*?|gather\*?|align\*?)\}[\s\S]*?\\label\{([^}]*)\}[\s\S]*?\\end\{(?:equation\*?|gather\*?|align\*?)\}/g;
  let count = 0;
  const map = {};
  let match;
  while ((match = regex.exec(text)) !== null) {
    const label = match[1];
    if (!map[label]) {
      count += 1;
      map[label] = count;
    }
  }
  return map;
}

function extractTitleAuthor(text) {
  const titleMatch = text.match(/\\title\{([^}]*)\}/);
  const authorMatch = text.match(/\\author\{([^}]*)\}/);
  const title = titleMatch ? titleMatch[1].trim() : null;
  let authors = authorMatch ? authorMatch[1] : null;
  if (authors) {
    authors = authors.replace(/\\And/g, ',').replace(/\s+/g, ' ').replace(/\s*,\s*/g, ', ').trim();
  }
  return { title, authors };
}

function applyTitleAuthor(text, meta, mode) {
  if (!meta) return text;
  let out = text.replace(/\\title\{[^}]*\}\s*/g, '').replace(/\\author\{[^}]*\}\s*/g, '');

  const lines = [];
  if (meta.title) {
    lines.push(mode === 'markdown' ? `# ${meta.title}` : `\\section*{${meta.title}}`);
  }
  if (meta.authors) {
    lines.push(mode === 'markdown' ? `*${meta.authors}*` : `\\textit{${meta.authors}}`);
    lines.push(mode === 'markdown' ? '---' : '\\\\[6pt]\\hrule');
  }

  if (lines.length) {
    out = `${lines.join('\n')}\n\n${out}`;
  }

  return out;
}

function renderPaperList(activeId) {
  const listEl = document.getElementById('paper-list');
  if (!listEl) return;
  if (!PAPERS.length) {
    listEl.innerHTML = '<p class="muted">No papers added yet.</p>';
    return;
  }

  listEl.innerHTML = '';
  PAPERS.forEach(paper => {
    const btn = document.createElement('button');
    const bullet = document.createElement('span');
    bullet.className = 'bullet';
    const label = document.createElement('span');
    label.textContent = paper.title;
    btn.appendChild(bullet);
    btn.appendChild(label);
    if (paper.id === activeId) {
      btn.classList.add('active');
    }
    btn.addEventListener('click', () => selectPaper(paper));
    listEl.appendChild(btn);
  });
}

function selectPaper(paper) {
  const params = new URLSearchParams(window.location.search);
  params.set('paper', paper.paper);
  if (paper.bib) {
    params.set('bib', paper.bib);
  } else {
    params.delete('bib');
  }
  const newSearch = params.toString();
  history.replaceState(null, '', `${window.location.pathname}${newSearch ? `?${newSearch}` : ''}`);
  loadPaper({ id: paper.id, title: paper.title, paperPath: paper.paper, bibPath: paper.bib });
}

function resetPanels() {
  const paperEl = document.getElementById('paper-content');
  const sidePanel = document.getElementById('side-panel-body');
  if (paperEl) {
    paperEl.innerHTML = '<p class="muted">Loading main paper…</p>';
  }
  if (sidePanel) {
    sidePanel.innerHTML = '';
    sidePanel.className = 'proof-placeholder';
  }
}

function updatePaperSubtitle(text) {
  const subtitle = document.querySelector('.paper-panel .panel-subtitle');
  if (subtitle) {
    subtitle.textContent = `Rendered from ${text}`;
  }
}

function escapeHtml(str) {
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}
