# Correction Note — σ-convention bug (session 90, 2026-05-21)

**Severity:** affects every theorem in `JepaRhoRecovery/` that consumes the
Bernoulli ODE form
`σ̇ = Lλσ^{3-1/L}·(1 − σ^{1/L}/ρ)` or the plateau formula `σ^∞ = ρ^L`.

## What the bug is

Paper-1 (`jepa-learning-order/JepaLearningOrder/JEPA.lean`) asserts the
above ODE form in the statement of `diagAmp_ODE` (line 665) and uses
plateau threshold `p · ρ^L` in `bernoulli_laurent_bound` (line 742),
`actual_critical_time` (line 848), and `JEPA_dynamics_ordering`
(`MainTheorem.lean` line 235). Empirical validation under aligned init
shows the **correct** ODE form is Saxe-style:
`σ̇ ∝ σ^{2-1/L}·(ρ − σ^L)`, with plateau `σ^∞ = ρ^{1/L}`.

## Why the Lean didn't catch it

`diagAmp_ODE`'s proof picks `C := max(C', 1)/ε^{(2L-1)/L}` from a
compactness bound, making the conclusion `|residual| ≤ C·ε^{(2L-1)/L}`
trivially true regardless of which ODE form sits in the statement. So
the form is *asserted* in the statement but *not constrained* by the
proof. The downstream Aristotle-proved theorems are
**algebraically consistent under the wrong form** but disconnected from
JEPA dynamics.

## Empirical evidence

See `experiments/RESULTS_session90_verification.md`. Under aligned init
`Wbar(0) = ε·I`, the encoder diagonal converges to `√ρ_r = ρ_r^{1/L}`
to 4e-4 precision; recovery `ρ̂ := σ^L` matches `ρ` at 6e-4 (sample-noise
floor); recovery `ρ̂ := σ^{1/L}` (paper formula) is off by 0.47.

Per-feature ODE-form fit (`experiments/ode_form_fit.py`): paper-1 form
predicts `σ̇ < 0` for 4 of 6 features that empirically are still growing.
Sign-wrong, not just magnitude.

## Affected Lean theorems (paper-2 only — paper-1 is a separate audit)

| Theorem | File | Disposition |
|---|---|---|
| `rho_hat_plateau_rate` | `JepaRhoRecovery/PlateauEstimator.lean` | **needs re-derivation** (input plateau target & output estimator exponent both flip) |
| `lambda_hat_early_slope_rate` | `JepaRhoRecovery/PlateauEstimator.lean` | **likely survives** — early-time leading term is the `λ σ^{3-1/L}` part regardless of bracket |
| `mu_hat_combination_rate` | `JepaRhoRecovery/PlateauEstimator.lean` | **likely survives** — algebraic identity in λ̂, ρ̂ |
| `sigma_positive_branch_converges` | `JepaRhoRecovery/SignedODE.lean` | **needs re-derivation** — qualitative plateau target flips to ρ^{1/L} |
| `signed_recovery_pos_magnitude_plateau` | `JepaRhoRecovery/SignedRecovery.lean` | **needs re-derivation** — Lyapunov V := (σ − ρ^L)² becomes V := (σ − ρ^{1/L})² |
| `early_slope_perturbation_pos` | `JepaRhoRecovery/SignedRecovery.lean` | **needs review** — Grönwall structure may transfer |
| `signed_recovery_neg_lambda_rate` | `JepaRhoRecovery/SignedRecovery.lean` | **needs review** — negative branch v-transform, may transfer |
| `early_slope_gronwall_bound` | `JepaRhoRecovery/EarlySlopeGronwall.lean` | **needs review** — v-transform helper |
| `plateau_path_recovery_pos` | `JepaRhoRecovery/Main.lean` | **needs re-derivation** — composes plateau + magnitude |
| `plateau_path_finite_sample_rate_pos` | `JepaRhoRecovery/FiniteSample.lean` | **statement update**, composition |
| `plateau_path_finite_sample_rate_pos_high_prob` | `JepaRhoRecovery/FiniteSample.lean` | **statement update**, composition |
| `matrix_bernstein_subgaussian` (axiom) | `JepaRhoRecovery/Concentration.lean` | unaffected (cites Tropp 2015) |

## Disposition for THIS session (session 90)

**No Lean math edits this session.** Build is currently green at 8041
jobs with 0 sorries; touching ODE forms would cascade and is best done
deliberately with Aristotle dispatch ready.

What this session DOES:
1. Documents the bug here.
2. Adds `-- ⚠ CORRECTION NOTE: see ../CORRECTION_NOTE.md` markers at the
   affected theorems (no math change).
3. Patches paper-2 text (`my_theorems/paper_draft.md`,
   `experiments/ALGORITHM_AND_EXPERIMENT_PLAN.md`) with the corrected
   formula and a visible CORRECTION NOTE.

## Disposition for NEXT session

Two routes are both reasonable; pick one:

**Route A — Local paper-2 patch (smaller, faster).**
1. Edit each affected theorem's statement in place (σ^L ↔ σ^{1/L},
   ρ^L ↔ ρ^{1/L}). Mark proofs that no longer compose with `sorry`.
2. Re-derive `rho_hat_plateau_rate` by hand (it's just algebra:
   `|σ^L − ρ| ≤ L · max(σ, ρ^{1/L})^{L-1} · |σ − ρ^{1/L}|`).
3. Dispatch 1-2 Aristotle jobs for whichever bridges don't survive
   straightforward re-derivation.
4. Leaves paper-1 alone; treats its bug as "out of scope" for paper-2.

**Route B — Full re-derivation (bigger, more honest).**
1. Patch paper-1 `JEPA.lean` first: ODE form, hitting threshold.
2. Re-derive `bernoulli_laurent_bound` Laurent expansion under the
   corrected ODE — Aristotle job, moderate difficulty.
3. Patch `actual_critical_time` and `JEPA_dynamics_ordering`.
4. Then patch paper-2 (which becomes mechanical once paper-1 is done).
5. Decide whether paper-1's published ordering result needs an
   erratum.

Route A is recommended unless paper-1 itself needs to be re-released.
The empirical ordering claim of paper-1 survives (it's about *direction*
of trajectory motion, which is correct under both ODE forms); only the
*quantitative bounds* would change.

## Reproducer

```bash
cd /Users/davidgoh/LocalFiles/lean-workspace/jepa-rho-recovery/experiments

# (1) Confirm σ^∞ = ρ^{1/L} under aligned init
python aligned_init_probe.py

# (2) Confirm ODE form mismatch (paper-1 vs Saxe)
python ode_form_fit.py

# (3) Run corrected algorithm; observe error at noise floor across ε
python plateau_recover_corrected.py
```
