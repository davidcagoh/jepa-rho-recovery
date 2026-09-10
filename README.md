# jepa-rho-recovery

Lean 4 formalization and supporting material for the AIS 2026 paper:

> **Signed Decomposition of the Regression Structure via Linear JEPA Training**

The paper studies how depth-$L$ linear JEPA training recovers the signed
regression structure from gradient-flow trajectories. The formalization covers
the main signed-decomposition result together with supporting ODE, recovery,
finite-sample, and zero-branch results.

## Paper

- [AIS 2026 camera-ready paper](paper/signed-decomposition.pdf)
- [Paper source](paper/src/)
- [Full-proof supplement](full-proofs/full-proofs.pdf)
- [Supplement source](full-proofs/full-proofs.tex)

The camera-ready paper uses proof sketches for five results to stay within the
venue's 15-page limit. The supplement gives their complete derivations:
`prop:diagonal-ode`, `prop:plateau`, `prop:neg-lambda`,
`cor:finite-sample-end`, and `thm:trichotomy`.

## Lean development

Build the formalization with:

```bash
lake build
```

The Lean catalogue in the paper's appendix maps paper propositions and theorems
to their Lean targets and discloses the two named axioms used for standard
matrix-concentration and scalar-ODE facts.

The companion feature-learning-order formalization is available at
[`davidcagoh/jepa-learning-order`](https://github.com/davidcagoh/jepa-learning-order).

## License and scope

This repository contains the Lean development, paper source, paper PDF, and
supporting derivations. Experimental notes are retained where they document the
computational validation of the paper's claims.
