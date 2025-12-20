# LeanPaper Site

Static, browser-only renderer for `core.tex` with MathJax and a LaTeX.js fallback. Intended to sit alongside the Lean formalization so the left panel shows the paper and the right panel can later surface Lean proofs.

## Quick start

```bash
npm install
npm run dev   # serves at http://localhost:8000
```

Your default browser can open `http://localhost:8000` to view `index.html`. The renderer fetches `core.tex` from the repo root, renders math with MathJax, and falls back to LaTeX.js if you pass `?renderer=latexjs` in the URL.

## Notes

- MathJax runs from CDN; no build step required.
- Dependencies `latex.js` and `marked` are listed for completeness/offline bundling, but the default page currently loads them via CDN.
- Right-hand Lean panel is a placeholder; hook it up to your Lean files when ready.
