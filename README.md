# jepa-rho-recovery

**Sequel to `jepa-learning-order`.** Lean 4 + paper project for the full
$\rho^*$-recovery theorem for depth-$L$ linear JEPA — Layers 1–5 of the
March 2026 recovery roadmap (`../jepa-learning-order/my_theorems/paper2_recovery/roadmap.md`).

## Headline framing (option 2 — moonshot)

> **JEPA training induces a signed decomposition of the regression structure.**
> Positive generalised regression coefficients $\rho_r^* > 0$ are learned with
> recoverable magnitude (inversion formula from critical times); negative
> coefficients are identified by their *suppression timescale*; the sign of
> $\rho_r^*$ is read off the gradient-flow trajectory itself.

This reframes the Layer-4.2(iii) "negative magnitudes unrecoverable from
JEPA alone" obstruction as a *structural* result — sign identification —
instead of a gap.

## Scope (all five layers)

| Layer | Theorem | Status |
|---|---|---|
| 1.1 | Rigorous quasi-static ODE hypothesis | hand-port (not Aristotle target) |
| 1.2 | Non-vacuous feature ordering (explicit $\epsilon_0$) | hand-port |
| 2.1 | Generalised diagonal ODE | pending |
| 2.2 | Identifiability / inversion formula $\hat\rho_r$ | **first Aristotle target — `Inversion.lean`** |
| 3.1 | Generalised-eigenvalue perturbation under sample noise | needs Mathlib lift |
| 3.2 | End-to-end finite-sample rate | depends on 3.1 |
| 4.1 | Signed-$\rho$ ODE analysis (suppression timescale) | **headline-B** |
| 4.2 | Signed recovery — magnitude (positive) + sign (all) | **headline-C** |
| 5.1 | Mixed-sign ordering | bookkeeping |

## Workspace context

Part of the **Stochastic Proofs** workspace. Shares the `../.lean-packages/`
Mathlib cache. Workflow conventions live in `../stochastic-proofs-handbook/`;
project state in `../wiki/INDEX.md` (OQ-17).

## Build

```bash
lake build
```

## Provenance

Repo created 2026-05-17 (session 67) after option-2 (full Layers 1–5
moonshot) was selected over option-1 (Layers 1–2 only TMLR follow-up).
See `../wiki/decisions.md` and OQ-17 in `../wiki/INDEX.md`.
