# Full proofs

Supplementary material for the AIS 2026 camera-ready paper *Signed Decomposition of
the Regression Structure via Linear JEPA Training* (David Goh).

`full-proofs.tex` / `full-proofs.pdf` contain the full derivations for five results
that the paper itself states with a proof sketch rather than the complete argument,
purely for page-budget reasons (a hard 15-page cap). Nothing here is new
mathematics: every derivation was already written out in full in a prior draft of
the paper and was moved here verbatim, not re-derived, when the corresponding
main-text proof was shortened. Each section is headed by the exact LaTeX `\label{}`
the result carries in the paper's own source, so a reader can match sketch to full
proof unambiguously without relying on section/theorem numbers, which can drift
independently in either document.

Covers: `prop:diagonal-ode`, `prop:plateau`, `prop:neg-lambda`,
`cor:finite-sample-end`, `thm:trichotomy`.

The document is self-contained — its own preamble, does not `\input` anything from
the paper's own build tree — and compiles independently:

```
pdflatex full-proofs.tex
```

## Relative to the rest of this repository

`ais-submission/` and `my_theorems/` are earlier, stale snapshots (May/June 2026)
that predate the camera-ready rewrite this document supplements — do not treat
either as current. This directory is the only paper-adjacent material in this
repository that's kept in sync with the actual submitted paper.
