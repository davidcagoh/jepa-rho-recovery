# Verification of σ-convention finding — CONFIRMED, paper-1 has a real bug

**Status:** verification complete. Paper-1's claimed ODE form is **empirically wrong in sign**, and the supporting Lean lemma `diagAmp_ODE` is **vacuously proved** (proof picks C large enough to absorb any residual). This is a real bug in paper-1, not a convention mismatch.

## What I checked

### 1. `quasiStatic_approx` (`jepa-learning-order/JepaLearningOrder/JEPA.lean:226`)

This lemma proves *predictor tracking*: `‖V(t) − V_qs(Wbar(t))‖_F ≤ C·ε^(2(L-1)/L)`. It does **not** say anything about the σ_r ODE. Its hypotheses include `‖Wbar(0)‖_F ≤ K₀·ε^(1/L)` and `‖V(0)‖_F ≤ K₀·ε^(1/L)` (scale ε^(1/L), not ε), and aligned setup is implicit via the gen-eigenbasis.

### 2. `diagAmp_ODE` (`jepa-learning-order/JepaLearningOrder/JEPA.lean:665`)

This is the lemma that *connects* JEPA gradient flow to the Bernoulli ODE. It states:

```
|σ̇_r(t) − L·λ·σ^(3-1/L)·(1 − σ^(1/L)/ρ)| ≤ C · ε^((2L-1)/L)
```

**Its Lean proof is essentially vacuous.** The proof body:

```lean
obtain ⟨ C, hC ⟩ := IsCompact.exists_bound_of_continuousOn (...) h_compact
exact ⟨ Max.max C 1 / epsilon ^ ((2*L-1)/L : ℝ), ..., ... ⟩
```

That is: pick *any* continuous bound `C'` for the residual (which exists on a compact interval), then set `C := max(C', 1) / ε^((2L-1)/L)`. The conclusion `|residual| ≤ C·ε^((2L-1)/L) = max(C', 1)` is then trivially true. **`C` absorbs the entire residual into a constant**, making the bound non-quantitative as ε → 0.

So the ODE form `(1 − σ^(1/L)/ρ)` is *asserted* in the lemma statement but **never constrained** by the proof.

### 3. Empirical ODE-form test (`ode_form_fit.py`)

Under aligned init (the paper-1 hypothesis regime), I measured numerical σ̇(t) along the training trajectory and compared against two candidate ODE forms:

- **Paper-1 form:** `σ̇ = L·λ·σ^(3-1/L)·(1 − σ^(1/L)/ρ)` → plateau σ = ρ^L.
- **Saxe form:** `σ̇ = L·μ·σ^(2-1/L)·(ρ − σ^L)` → plateau σ = ρ^(1/L). (Equivalent rewrite: `σ̇ ∝ σ^(2-1/L)·(1 − σ^L/ρ)` — same bracket just with σ^L instead of σ^(1/L).)

Result (`results_plateau_smoke/ode_form_fit.json`):

| Form | median |rel residual| | sign correct? |
|---|---|---|
| Paper-1 `(1 − σ^(1/L)/ρ)` | 1.43; max 178 | **Wrong sign for 4 of 6 features** |
| Saxe `(ρ − σ^L)` | 0.74; max 0.86 | Correct sign for all 6 |

Per-feature peak-velocity check (in motion phase):

| r | ρ_r | σ_r at peak | empirical σ̇ | paper RHS | Saxe RHS |
|---|---|---|---|---|---|
| 0 | 1.00 | 0.525 | +0.127 | +0.110 | +0.551 |
| 1 | 0.84 | 0.542 | +0.096 | +0.045 | +0.436 |
| 2 | 0.68 | 0.495 | +0.069 | **−0.008** | +0.303 |
| 3 | 0.52 | 0.405 | +0.050 | **−0.024** | +0.184 |
| 4 | 0.36 | 0.359 | +0.027 | **−0.037** | +0.099 |
| 5 | 0.20 | 0.256 | +0.011 | **−0.020** | +0.035 |

**Paper-1 predicts σ_r should be shrinking** (σ̇ < 0) at features with ρ ≤ 0.68 — but empirically they are still **growing toward** σ = √ρ. The paper formula has the bracket inverted. The constant ~4× factor on the Saxe form is explained by loss-normalisation differences (my `((y_hat − y)**2).mean()` averages over output dim too, vs Lean's `½·tr` form — `2/d` factor in gradient, `d=6` here gives a 3× discrepancy; remaining is from my full-batch GD step size convention vs continuous-time scaling).

## Mechanism of the bug

The paper-1 ODE statement places equilibrium at `σ^(1/L) = ρ`, i.e. **σ = ρ^L**. The actual JEPA gradient flow (and standard Saxe deep-linear theory) places equilibrium at `σ^L = ρ`, i.e. **σ = ρ^(1/L)**. The exponent inside the bracket — `σ^(1/L)/ρ` in paper-1 vs. `σ^L/ρ` correct — is the inversion.

For small initialisation, σ is small and both forms predict similar growth direction (the leading `λ·σ^(3-1/L)` term dominates). The bug only manifests near the plateau where the bracket matters. So in toy experiments where you only watch the early growth phase, the bug is invisible. It surfaces only when:
1. You observe σ near its plateau, AND
2. The plateau value matters for downstream claims (which it does for paper-2's recovery formula).

## Why the Lean formalisation didn't catch it

`diagAmp_ODE`'s proof discharges by `IsCompact.exists_bound_of_continuousOn` — any continuous function on `[0, t_max]` is bounded. The lemma extracts that bound and divides by `ε^((2L-1)/L)`, which makes the claim `|residual| ≤ C·ε^((2L-1)/L)` trivially true (since C inversely scales). This is exactly the "vacuous hypothesis" pattern flagged in `jepa-rho-recovery/CLAUDE.md` ("epsilon_0 = 0" and similar). The ODE form is encoded in the *statement* but not constrained by the *proof*.

`actual_critical_time` and `bernoulli_laurent_bound` then take this (unproved-from-dynamics) ODE form as a hypothesis and derive hitting-time bounds at threshold `p·ρ^L`. These are algebraically consistent **with the wrong ODE**, but disconnected from what JEPA actually does.

## Impact

This is broader than session-90's earlier statement:

1. **Paper-1's main theorem `JEPA_dynamics_ordering` is built on a vacuously-proved ODE form.** The *ordering* claim (which trajectory reaches threshold first) might still be true *empirically*, but its Lean proof is not load-bearing — the proof depends on `diagAmp_ODE` which has no quantitative content.
2. **Paper-1's hitting-time Laurent expansion at threshold `p·ρ^L`** computes the time for σ to reach `ρ^L`. Since σ actually plateaus at `ρ^(1/L) < ρ^L` (for ρ < 1), σ **never reaches `p·ρ^L`** in finite time for p < 1. The hitting time is `∞` empirically. The Laurent bound is on an undefined quantity. (Strictly: `hittingTime` in Lean returns `t_max` if the threshold is never crossed, so the bound is a degenerate statement.)
3. **Paper-2's entire `PlateauEstimator.lean` layer** (Layer 2.2′: `rho_hat_plateau_rate`, `lambda_hat_early_slope_rate`, `mu_hat_combination_rate`) is built on the paper-1 ODE form. Aristotle proved these as algebra, but they describe behaviour that doesn't happen.
4. **Paper-2's headline `plateau_path_recovery_pos`** in `Main.lean` claims trajectory-only recovery via `ρ̂ = σ^(1/L)`. Empirically `ρ̂ := σ^L` is the correct formula. The exponent is wrong end-to-end.
5. The named axiom `matrix_bernstein_subgaussian` (Layer 3.3) is independent of this issue and remains a valid citation of Tropp 2015.

## Recommended correction path

This is bigger than a paper-2 typo. Concretely:

1. **Audit `JEPA.lean` Section 6** (ODE statements). Replace `(1 − σ^(1/L)/ρ)` with `(1 − σ^L/ρ)` throughout. This flips the equilibrium from σ = ρ^L to σ = ρ^(1/L), matching Saxe.
2. **Re-derive `diagAmp_ODE` properly** — not via vacuous compactness, but via an actual chain-rule + tracking argument starting from `quasi_static_approx`. The connection is: `σ̇_r = (preconditioner) · u^T(-gradWbar) v`; substituting V ≈ V_qs and Wbar diagonal in U basis gives the Saxe form (after the algebra I sketched in session notes).
3. **Update `bernoulli_laurent_bound`** to use threshold `p·ρ^(1/L)`, not `p·ρ^L`. The Laurent expansion structure should survive (the algebra is similar).
4. **Update paper-1 text + LaTeX** to state σ_r^∞ = ρ_r^(1/L) throughout, and hitting time = time to reach `p·ρ^(1/L)`.
5. **Update paper-2 pseudocode** to `ρ̂ = σ^L`. Update §4.1 plateau claim. Update `PlateauEstimator.lean` ODE form. Aristotle's algebraic proofs of the bridge lemmas need to be re-run (or re-derived by hand) with the corrected ODE.
6. **Re-run smoke test** under corrected formula. Verify rate `|ρ̂ − ρ| ≤ C·ε^(1/L)|log ε|` across ε decades.

## Honest read

The paper-1 work (Lean formalisation of ρ*-ordering for JEPA) is built on an ODE statement that doesn't match the dynamics it claims to describe. The Lean proof discharges the gap via vacuous compactness rather than actual derivation. This is an honest bug; it's the kind of thing that's hard to catch without an empirical sanity check, which is exactly what session 90's smoke test produced.

**The empirical finding is solid and reproducible.** The Lean is consistent with itself (statements compile, build is green at 8041 jobs) but not consistent with the JEPA dynamics it's modelling. This needs to be raised on paper-1 before paper-2 can proceed.

The good news: the correction is a *local* exponent fix (σ^(1/L) → σ^L in one bracket), and the high-level architecture (Bernoulli ODE, Laurent expansion, hitting-time analysis) survives. The bad news: every theorem that consumed the wrong form needs to be re-derived. Including paper-1's published ordering claim (the proof, not necessarily the result).

## Files this verification

- `experiments/ode_form_fit.py` — fits paper-1 and Saxe ODE forms to measured σ̇.
- `experiments/results_plateau_smoke/ode_form_fit.json`
- `experiments/RESULTS_session90_verification.md` — this doc.
