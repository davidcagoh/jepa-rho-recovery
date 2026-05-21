# Session-90 smoke test — paper-2 algorithm empirical validation

**Status:** smoke test ran; **σ-convention discrepancy uncovered between paper-2 text and the natural Python implementation**. Headline rate validation is blocked on resolving the convention. No Lean changes this session. Two new diagnostic scripts committed under `experiments/`.

## What was run

1. `experiments/plateau_recover_smoke.py` — minimal `plateau_recover()` per `ALGORITHM_AND_EXPERIMENT_PLAN.md` §2.2. Depth-2 linear JEPA, d=10, full-batch GD, lr=0.05, 30 000 steps, ε ∈ {1e-1, 3e-2, 1e-2, 3e-3}, 3 seeds.
2. `experiments/sigma_convention_probe.py` — compares three σ-conventions against the paper's claim σ^∞ = ρ^L on the same setup.

Outputs at `experiments/results_plateau_smoke/`.

## Headline finding — σ-convention mismatch

The Lean `diagAmplitude` definition (`JepaRhoRecovery/Basic.lean:104`) is
$$\sigma_r := u_r^\top \bar W\, v_r^*$$
with `u_r = Σ^xx v_r` the dual basis. On the synthetic setup (Σ^xx = U U^T, Σ^yx = U diag(ρ) U^T, μ_r ≡ 1), the dual basis collapses to `u_r = U[:,r]`.

After training W̄ to convergence (W̄ → R = U diag(ρ) U^T), the empirical plateau is:

| Convention | Definition | Predicted plateau | Measured plateau |
|---|---|---|---|
| **A (Lean `diagAmplitude`)** | `u_r^T W̄ v_r` | `ρ_r` | **`ρ_r` (error 1.1e-3)** |
| B | `\|U^T W̄ U\|_{rr}` | `\|ρ_r\|` | `\|ρ_r\|` (error 1.1e-3) |
| C (per-layer geomean) | geomean of layer `\|U^T W_ℓ U\|_{rr}` | `\|ρ_r\|^{1/L}` | does not match (off-diagonal energy non-trivial) |
| **Paper §4.1 claim** | σ^∞ = ρ^L | `ρ_r^L = ρ_r^2` (L=2) | **error 0.2485 against σ_A** |

Numerical evidence (`ρ* ∈ [1.0, 0.911, …, 0.2]` linearly spaced; d=10, L=2):

```
rho_star          : +1.000  +0.911  +0.822  +0.733  +0.644  +0.556  +0.467  +0.378  +0.289  +0.200
σ_A (W̄ diagonal) : +1.000  +0.911  +0.821  +0.733  +0.644  +0.556  +0.466  +0.378  +0.289  +0.200
Paper claim ρ^L  : +1.000  +0.830  +0.676  +0.538  +0.415  +0.309  +0.218  +0.143  +0.083  +0.040
‖σ_A − ρ^L‖∞ = 0.2485   ‖σ_A − ρ‖∞ = 0.0011
```

**The natural diagonal amplitude does *not* plateau at ρ^L. It plateaus at ρ.** The pseudocode formula `ρ̂ = sign(σ)·|σ|^{1/L}` in §2.2 of the plan therefore returns `sign(ρ)·|ρ|^{1/L}` (e.g. 0.448 instead of 0.200), with `err_inf ≈ 0.25` and *no* ε-dependent improvement (the bias is structural).

Using the empirically validated `ρ̂_native = σ_A` recovery, all four ε-values reach `err_inf ≈ 5e-4` (sample-noise floor), independent of ε — i.e. once W̄ reaches the regression matrix R, recovery is sample-limited not ε-limited.

## Implications

Three plausible explanations for the mismatch — each has different downstream impact:

1. **Lean def matches paper convention, but the paper claim σ^∞ = ρ^L is wrong.** The Bernoulli ODE `σ̇ = λ σ^{3-1/L} - μ σ^3` would then need re-derivation. (Likely: the actual ODE for σ_A = u^T W̄ v under balanced depth-L flow is `σ̇ = (something) · (ρ - σ)^{...}` with plateau ρ.) This invalidates §4.1–§5.1 derivations as written. The Aristotle-proved `sigma_positive_branch_converges` may still be valid for *its actual statement*; the audit is what plateau it concludes to.
2. **Paper uses a different `σ`-convention than `diagAmplitude`.** For example, paper-1's underlying ODE may use σ := `(u^T W̄ v)^L` (a rescaling). In that case the algorithm pseudocode is wrong; correct recovery is `ρ̂ = (σ_A^{1/L})^L = σ_A` directly, with **no exponent**.
3. **Paper convention is for a different W̄.** If `W̄` in the paper is *not* the full composition but the encoder of a single-layer-encoder-with-L-fold-feedback model, then σ_A might naturally plateau at ρ^L. Need to inspect the paper-1 → paper-2 transplant of the JEPA model.

I cannot resolve which one without re-reading the paper-1 ODE derivation against `JepaRhoRecovery/Basic.lean`. **This is the next-session blocker.**

## What still empirically holds

- **Ordering is recovered cleanly.** Final σ_A respects the ρ-ordering with no inversions across seeds. Paper-1 result is unaffected by this finding.
- **Trajectory ordering across critical times** also holds (verified in session-86 sweep results).
- **Sample-noise floor under full-batch GD on n=4096 is ~5e-4**, consistent with `n^{-1/2}·noise_std ≈ 3e-4`. Tier-1 n-sweep can proceed once the convention question is settled.

## Quasi-static residual diagnostic

The diagnostic in `quasi_static_residual()` measures
$$r(t) := \dot\sigma_r - (\lambda_r \sigma_r^{3-1/L} - \mu_r \sigma_r^3)$$
against the paper's claimed ODE. Global mean relative residual ≈ 30–50 across the trajectory — i.e. the measured σ_A does *not* satisfy this ODE (within an order of magnitude or even close). This is consistent with the σ-convention finding: if σ_A's true ODE has the form `σ̇ ∝ (ρ − σ)` rather than `λ σ^{3-1/L} - μ σ^3`, the residual against the latter is structurally large.

**Until the σ-convention is reconciled, the quasi-static empirical smoke test (S+3 in the algorithm plan) is uninterpretable.**

## Files this session

- `experiments/plateau_recover_smoke.py` — minimal algorithm + ε-sweep driver (260 LoC).
- `experiments/sigma_convention_probe.py` — convention diagnostic (110 LoC).
- `experiments/results_plateau_smoke/smoke_results.json` — ε-sweep data.
- `experiments/results_plateau_smoke/sigma_conventions.json` — convention comparison.
- `experiments/RESULTS_session90_smoke.md` — this doc.

## What to do next session

1. **Reconcile σ-convention.** Read `JepaRhoRecovery/Basic.lean` `diagAmplitude` against the paper-1 ODE derivation (`jepa-learning-order/JepaLearningOrder/...`). Decide which of (1)/(2)/(3) above is the actual situation. The decision rewrites either:
   - Paper-2 §4.1 (ODE statement + plateau formula), or
   - The algorithm pseudocode (drop the `1/L` exponent), or
   - The Lean `diagAmplitude` definition (rare; should be last resort).
2. Once reconciled, re-run the ε-sweep with the corrected estimator. Verify the rate against theory (whatever theory predicts in the corrected convention).
3. Re-derive the quasi-static residual against the corrected ODE; smoke-test it.
4. Only then proceed to Tier-1 sweeps (n, L, ε) for paper-2 §7.

## Honest read

The previous-session ALGORITHM_AND_EXPERIMENT_PLAN.md and paper §4–§5 were written without an empirical sanity check on the pseudocode. The first real test surfaced a definition/convention bug — exactly what an S+1 smoke test is meant to surface. **This is a successful outcome of running the smoke test before committing to the full library investment**, even though it surfaces a problem rather than confirming readiness.

The Lean theorems are not invalidated by this finding — they may already be self-consistent under a single convention. What needs to change is either the paper text's narrative about what σ means, or the algorithm pseudocode's exponent. Either is a focused fix once the convention is pinned down.
