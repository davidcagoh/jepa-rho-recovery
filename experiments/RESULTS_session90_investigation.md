# Session-90 σ-convention investigation — RESOLVED

**Status:** σ-convention crisis from earlier this session is **resolved**. The paper formula `ρ̂ = σ^(1/L)` is wrong; the correct formula is `ρ̂ = σ^L`. Paper-1's stated plateau `σ^∞ = ρ^L` is wrong; the correct plateau is `σ^∞ = ρ^(1/L)`. The exponent is inverted in the paper-1 ODE form and propagated to paper-2.

## Investigation path

1. Read `jepa-learning-order/JepaLearningOrder/JEPA.lean:848 actual_critical_time`. ODE form is `σ̇ = L·λ·σ^(3-1/L) · (1 − σ^(1/L)/ρ)`. Setting σ̇=0: equilibrium at σ = ρ^L. Hitting target `p · ρ^L` matches.
2. Read `jepa-learning-order/JepaLearningOrder/MainTheorem.lean:235 JEPA_dynamics_ordering`. The Bernoulli ODE and `σ_r(0) = ε` are **hypotheses**, not derived from JEPA dynamics — meaning they specify a *particular* initialisation regime, not a generic small-init.
3. Ran `aligned_init_probe.py` with `Wbar(0) = ε·I` (the init that exactly satisfies `σ_r(0) = ε`). Trained both V and Wbar under JEPA loss to convergence.

## Empirical result (`results_plateau_smoke/aligned_init.json`)

| Quantity | Value | What it implies |
|---|---|---|
| σ_r(0) (initialisation) | `0.05` for all r | matches paper-1 hypothesis ✓ |
| σ_r(∞) (after 80 k steps) | matches **√ρ_r** to 4e-4 | plateau is `ρ^(1/L)`, **not** `ρ^L` |
| ‖σ^L − ρ‖∞ | 6.4e-4 | `ρ̂ := σ^L` recovers ρ at noise floor |
| ‖σ^(1/L) − ρ‖∞ | 0.469 | `ρ̂ := σ^(1/L)` (paper formula) is off by ~0.5 |
| Composition (V·Wbar) diagonal | matches **ρ** to 7e-4 | full composition does converge to R as expected |

For depth-2 the empirics give exactly the standard Saxe (2014) deep-linear result: each layer's amplitude converges to `√ρ`; the composition converges to `ρ`. **The paper-1 ODE form has its exponent inverted relative to the correct dynamics.**

## What the corrected ODE should look like

Empirically `σ_r → ρ_r^(1/L)`. For this to be the equilibrium of a Bernoulli-form ODE `σ̇ = α σ^a − β σ^b`:
- Need `α/β = σ^(b-a)` at equilibrium → `ρ = (ρ^(1/L))^(b-a)` → `b − a = L`.
- Standard Saxe form (2-layer): `σ̇ ∝ (ρ − σ²) · σ` → `b − a = 2 = L` ✓.

The paper-1 ODE `σ̇ = Lλ σ^(3-1/L)(1 − σ^(1/L)/ρ)` expands to `Lλ σ^(3-1/L) − Lλ/ρ · σ^3`, giving `b − a = 3 − (3 − 1/L) = 1/L`, so equilibrium `ρ = σ^(1/L)` → `σ = ρ^L`. That's the inverse direction from empirical.

**Likely intended form** (matching Saxe & matching the empirical σ → ρ^(1/L)):
```
σ̇ = L · μ · σ^(2-1/L) · (ρ − σ^L)
```
Equilibrium: `σ^L = ρ` → `σ = ρ^(1/L)` ✓. Or equivalently, swap `σ^(1/L)/ρ` ↔ `σ^L/ρ` in the paper-1 form.

## Impact on paper-2

1. **Pseudocode in `ALGORITHM_AND_EXPERIMENT_PLAN.md` §2.2 is wrong.** `rho_hat[r] = sign(σ)·|σ|^(1/L)` should be `rho_hat[r] = sign(σ)·|σ|^L`.
2. **Paper-2 §4.1 plateau claim `σ_r^∞ = (ρ_r^*)^L` is wrong.** Correct claim is `σ_r^∞ = (ρ_r^*)^(1/L)`.
3. **The headline rate `ε^(1/L)|log ε|` likely survives in direction.** Error |σ − ρ^(1/L)| should still scale as `ε^(1/L)·|log ε|` (this is what Saxe-style analysis gives). The conversion to `ρ̂ = σ^L` multiplies the rate by `L · ρ^((L-1)/L)` constants but preserves the ε-exponent.
4. **All trajectory bridge theorems in `JepaRhoRecovery/PlateauEstimator.lean`** (`rho_hat_plateau_rate`, `lambda_hat_early_slope_rate`, `mu_hat_combination_rate`) need their ODE forms audited. Aristotle proved them under the inverted ODE statements; the proofs may still be valid as algebra under the named axioms, but the *connection to JEPA dynamics* (Layer 1.1 quasi_static_approx) needs re-derivation.
5. **Paper-2's Bernoulli ODE in §4.1** also needs re-derivation. The form `σ̇ = λ σ^(3-1/L) − μ σ^3` is *not* the JEPA gradient-flow form for the standard `diagAmplitude` definition.
6. **The Aristotle-proved `quasi_static_approx` (job `1ccc1ab8`) is the load-bearing claim to re-audit.** It supposedly derives the Bernoulli ODE from JEPA dynamics. If that derivation is wrong, paper-1 has a bug; if it's right under a different σ convention, paper-2 needs to clarify which convention it uses end-to-end.

## What the empirical algorithm *should* do

The corrected `plateau_recover()` for the positive branch:

```python
def plateau_recover(X, Y, L, eps, ...):
    # Train depth-L JEPA with aligned init Wbar(0) ≈ ε · I in eigenbasis.
    # (Requires knowing the eigenbasis U up front from Σ̂_XX, Σ̂_YX.)
    ...
    sigma_T = u_r^T Wbar(T) v_r      # diag amplitude of encoder Wbar
    rho_hat[r] = sign(sigma_T) * abs(sigma_T) ** L     # σ^L, not σ^(1/L)
    return rho_hat
```

The aligned-init requirement is non-trivial: it requires knowing U from the sample covariances *before* training. For paper-2 this is fine — Step 2 of the pseudocode already computes U from `eig(Σ̂_YX, Σ̂_XX)`. The algorithm flow is unchanged; only the init scheme and the final exponent need correction.

## Files this investigation

- `experiments/encoder_diag_probe.py` — measures encoder vs composition under generic orthogonal init (showed gauge ambiguity).
- `experiments/aligned_init_probe.py` — measures under aligned `Wbar(0) = ε·I` init (showed σ → √ρ).
- `experiments/results_plateau_smoke/encoder_diag.json`
- `experiments/results_plateau_smoke/aligned_init.json`
- `experiments/RESULTS_session90_investigation.md` — this doc.

## Recommended next session

1. **Audit `quasi_static_approx` Aristotle proof (job `1ccc1ab8`)** in jepa-learning-order. Specifically: what plateau does it derive? Is the exponent really `σ^(1/L)/ρ` (paper form) or `σ^L/ρ` (correct form)? This is the load-bearing question.
2. If `quasi_static_approx` has the inverted exponent: file a bug, decide whether to (a) re-derive Layer 1.1 with the correct form, (b) re-interpret σ as a quantity that genuinely plateaus at ρ^L (possible if σ_paper := composition^L = (V Wbar)^L = ρ^L, but that's not what `diagAmplitude` measures).
3. If the Lean ODE is provably correct but for a different σ: rename the Python quantity, update the paper-2 algorithm pseudocode and §4.1 to use this σ explicitly (defined in terms of the Lean object), and re-run the smoke test.
4. Either way: paper-2's algorithm pseudocode in `ALGORITHM_AND_EXPERIMENT_PLAN.md` §2.2 needs to be patched. The simplest change (consistent with the empirics under aligned init): change `**(1/L)` to `**L` and add an "aligned init required" note.
5. Then re-run the smoke test ε-sweep and verify the rate `|ρ̂ − ρ| ≤ C · ε^(1/L)|log ε|` empirically across decades of ε.
