# jepa-rho-recovery

Lean 4 formalization and supporting material for the AIS 2026 camera-ready paper:

> **Signed Decomposition of the Regression Structure via Linear JEPA Training**

The paper studies how depth-$L$ linear JEPA training recovers the signed
regression structure from gradient-flow trajectories. This repository contains
the corresponding Lean development, the 15-page paper, and the complete
derivations moved to a supplement for the paper's page budget.

## Paper

- [AIS 2026 camera-ready paper](paper/signed-decomposition.pdf)
- [Paper source](paper/src/)
- [Full-proof supplement](full-proofs/full-proofs.pdf)
- [Supplement source](full-proofs/full-proofs.tex)

The camera-ready paper uses proof sketches for five results to stay within the
venue's 15-page limit. The supplement gives their complete derivations:
`prop:diagonal-ode`, `prop:plateau`, `prop:neg-lambda`,
`cor:finite-sample-end`, and `thm:trichotomy`.

## Formalization map

- `JepaRhoRecovery/Main.lean` — signed-decomposition theorem bundle across
  positive, negative, and zero branches, plus mixed-sign ordering.
- `JepaRhoRecovery/SignedRecovery.lean` — sign identification and positive- and
  negative-branch recovery bounds.
- `JepaRhoRecovery/FiniteSample.lean` — positive-branch, negative-branch, and
  uniform end-to-end finite-sample rate wrappers.
- `JepaRhoRecovery/ZeroBranchResidual.lean` — corrected residual-bearing
  zero-branch analysis at depth $L=2$.
- `JepaRhoRecovery/Concentration.lean` — the explicitly named matrix-Bernstein
  axiom used by the finite-sample development.

The paper appendix contains the theorem-by-theorem crosswalk, assumptions, and
axiom disclosure. The Lean statements are checked by the Lean kernel; a
theorem body being sorry-free is reported separately from its use of named
axioms.

## Lean development

Build the formalization with:

```bash
lake build
```

The current development builds successfully with the pinned toolchain and
Mathlib manifest in this repository.

To rebuild the paper PDF from source:

```bash
cd paper/src
latexmk -pdf signed-decomposition.tex
```

The companion feature-learning-order formalization is available at
[`davidcagoh/jepa-learning-order`](https://github.com/davidcagoh/jepa-learning-order).

## Scope

This is the public research artifact for the paper. It includes the Lean
development, camera-ready PDF, LaTeX source, full-proof supplement, and
computational validation notes. Reviewer correspondence, registration records,
submission credentials, and internal drafting material are kept outside the
repository.
