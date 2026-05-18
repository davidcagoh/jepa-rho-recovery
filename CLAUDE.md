# CLAUDE.md — jepa-rho-recovery

> **Current proof state and next priorities live in `../wiki/INDEX.md` (OQ-17), not here.**
> This file contains only architectural context that doesn't change session-to-session.

## Repository role

Lean 4 + paper project for the **full $\rho^*$-recovery theorem** for depth-$L$
linear JEPA. Spinoff from `../jepa-learning-order/` (which proves $\rho^*$-ordering).

Scope: all 5 layers of `../jepa-learning-order/my_theorems/paper2_recovery/roadmap.md`
(option 2 — moonshot). Target venue: COLT / JMLR (single big paper) or split as
arXiv pre-prints if the signed-decomposition framing matures faster than finite-sample
rates.

## Headline (option-2 framing)

JEPA training induces a **signed decomposition** of the regression structure:
- positive $\rho_r^*$: magnitude recovered via inversion of critical time $\tilde t_r^*$
- negative $\rho_r^*$: sign identified by suppression dynamics; magnitude from covariance
- zero $\rho_r^*$: no learning, no suppression

This reframes Layer-4.2(iii) (negative magnitudes unrecoverable from JEPA dynamics
alone) as a feature, not a gap.

## Relation to jepa-learning-order

| Concern | Source of truth |
|---|---|
| Generalised eigenbasis $(\mathbf{u}_r^*, \mathbf{v}_r^*)$ definitions | port / re-derive locally |
| `actual_critical_time`, `bernoulli_laurent_bound`, `JEPA_dynamics_ordering` | jepa-learning-order; cite, don't re-prove |
| Quasi-static `hV_flow` hypothesis | **rewritten here** (Layer 1.1 fixes its vacuity) |
| Feature-ordering $\epsilon_0$ witness | **rewritten here** (Layer 1.2 fixes the degenerate `0` witness) |

Decision: do **not** Lake-depend on `../jepa-learning-order` initially. Re-derive
shared definitions locally so the spinoff can evolve definitions freely without
breaking paper 1 builds. Re-evaluate after Layer 2.1 lands.

## File map (planned)

| Path | Role |
|---|---|
| `JepaRhoRecovery/Basic.lean` | Generalised eigenbasis + JEPA model types |
| `JepaRhoRecovery/QuasiStatic.lean` | Layer 1.1 — rigorous ODE quasi-static lemma |
| `JepaRhoRecovery/Ordering.lean` | Layer 1.2 — non-vacuous feature ordering |
| `JepaRhoRecovery/DiagonalODE.lean` | Layer 2.1 — generalised diagonal ODE reduction |
| `JepaRhoRecovery/Inversion.lean` | Layer 2.2 — identifiability inversion formula |
| `JepaRhoRecovery/SampleNoise.lean` | Layer 3.1 — perturbation under sample covariance |
| `JepaRhoRecovery/FiniteSample.lean` | Layer 3.2 — end-to-end finite-sample rate |
| `JepaRhoRecovery/SignedODE.lean` | Layer 4.1 — signed-$\rho$ ODE analysis |
| `JepaRhoRecovery/SignedRecovery.lean` | Layer 4.2 — sign identification theorem |
| `JepaRhoRecovery/MixedOrdering.lean` | Layer 5.1 — mixed-sign ordering |
| `JepaRhoRecovery/Main.lean` | Top-level signed-decomposition theorem |
| `my_theorems/paper_draft.md` | Bubeck-style paper outline (authoritative spec; auto-excluded from Aristotle tar) |
| `requests/` | Aristotle submission prompts |
| `results/` | Aristotle output records |

## Build commands

```bash
lake build
lake build JepaRhoRecovery.Basic
```

## Scripts

Use the shared handbook tooling:

```bash
python ../stochastic-proofs-handbook/scripts/status.py
python ../stochastic-proofs-handbook/scripts/submit.py requests/<file>.md "..."
python ../stochastic-proofs-handbook/scripts/retrieve.py <project-id>
```

## Architecture invariants (do not violate)

**Vacuity discipline.** This project exists *because* paper-1 carries
vacuously-satisfiable hypotheses (`∀ t, True`, `epsilon_0 = 0`). For every
lemma here:
1. Every hypothesis must be non-trivially constraining (no `True` placeholders,
   no `deriv f t = ...` on potentially non-differentiable `f`).
2. Every existential witness must be a *positive* quantity genuinely depending
   on problem parameters — never `0`.
3. The roadmap (Layer 1, Gap 1.1 + 1.2) is the canonical instruction.

**Signed framing.** Theorem statements should be in terms of *signed* $\rho_r^*$
from the start. Do not write a positive-only version "to be generalised later" —
that path produced paper-1's structural pain. The proof can branch by sign;
the *statement* must not.

**Paper draft is authoritative spec.** When `my_theorems/paper_draft.md` and Lean
diverge after an Aristotle run, paper takes precedence on mathematical
content; Lean takes precedence on what is actually proved.

## Strategic advice

**Don't ship paper-2 until headline-C (signed-decomposition theorem) is
sorry-free at statement level.** The moonshot value is the framing; without
4.2 the paper is "Layers 1–2 of a roadmap," which is option-1 we already
declined.

**Sequence** (revised session 67 per option-c handbook compliance):
- Layer 1.1, 1.2: hand-written ports/refactors of paper-1's proved
  `quasiStatic_approx` (Aristotle job 1ccc1ab8) and feature-ordering.
  **Not** Aristotle targets — re-asking wastes budget.
- **Theorem 2.2 (inversion formula): first Aristotle target.** Smallest new
  result, pure asymptotic analysis, no ODE machinery, lock-in for paper §5.
  Lives in `JepaRhoRecovery/Inversion.lean`.
- Then 4.1 → 4.2 (moonshot core), then fill back 2.1 / 3.x / 5.1.
