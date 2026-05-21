/-
Copyright (c) 2026. All rights reserved.
Released under MIT license.
Authors: David Goh

# Corrected Plateau Theorems (session 90, 2026-05-21)

Empirical validation (`experiments/RESULTS_session90_verification.md`)
identified that paper-1's Bernoulli ODE form

    σ̇ = L λ σ^{3-1/L} (1 − σ^{1/L}/ρ)

has its bracket exponent inverted. The correct (Saxe-style) form is

    σ̇ = L μ σ^{2-1/L} (ρ − σ^L)

with plateau σ^∞ = ρ^{1/L}, and the recovery estimator is ρ̂ := σ^L
(not σ^{1/L}).

This file collects the *corrected* versions of the three load-bearing
positive-branch theorems. Each statement parallels its inverted-form
counterpart in `PlateauEstimator.lean` / `SignedODE.lean` /
`SignedRecovery.lean`. Proofs are queued for Aristotle resubmit.

The three corrected lemmas:

1. `rho_hat_plateau_rate_corrected` — pure algebra,
   plateau hypothesis `|σ − ρ^{1/L}| ≤ K · ε^{1/L} |log ε|` gives
   the estimator bound `|σ^L − ρ| ≤ C · ε^{1/L} |log ε|`.
2. `sigma_positive_branch_converges_corrected` — qualitative
   convergence σ → ρ^{1/L} under the Saxe ODE.
3. `signed_recovery_pos_magnitude_plateau_corrected` — bridge
   from qualitative convergence to quantitative plateau rate.
-/

import JepaRhoRecovery.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

namespace JepaRhoRecovery

open Real Filter Topology

/-! ## §1. Corrected plateau-to-estimator algebraic lemma -/

/--
**Corrected Theorem 5.1′ (plateau → estimator, Saxe-form convention).**

Suppose the diagonal amplitude at observation time `T` satisfies
`|σ(ε) − ρ^{1/L}| ≤ K · ε^{1/L} · |log ε|`
for ε in `(0,1)`. Then the recovery estimator `ρ̂(ε) := σ(ε)^L` satisfies
`|ρ̂(ε) − ρ| ≤ C · ε^{1/L} · |log ε|` for ε below some threshold ε_0.

The constant `C` depends only on `L`, `ρ`, and `K` (via the bound
`L · (ρ^{1/L} + δ)^{L-1} · K` where `δ` is any margin that makes
σ stay bounded; the proof uses the small-ε regime to make δ ≤ ρ^{1/L}).

**Proof strategy** — pure algebra, no ODE. Use the factorisation

    a^L − b^L = (a − b) · Σ_{k=0}^{L-1} a^k b^{L-1-k}

with a = σ(ε), b = ρ^{1/L} (so a^L = σ^L, b^L = ρ). The sum is bounded
by `L · max(a, b)^{L-1}`. For ε small enough, `|σ − ρ^{1/L}| ≤ ρ^{1/L}/2`,
hence `σ ≤ (3/2) · ρ^{1/L}`, so `max(σ, ρ^{1/L})^{L-1} ≤ (3/2)^{L-1} · ρ^{(L-1)/L}`.
Combine for `C = L · (3/2)^{L-1} · ρ^{(L-1)/L} · K`.

This is the inverse of `PlateauEstimator.rho_hat_plateau_rate` (the
inverted-form version): there, the input plateau target was `ρ^L`
and the estimator was `σ^{1/L}`; here both are flipped.
-/
theorem rho_hat_plateau_rate_corrected
    (L : ℕ) (hL : 2 ≤ L)
    (rho : ℝ) (hrho_pos : 0 < rho)
    (sigma_at_T : ℝ → ℝ)
    (K_plateau : ℝ) (hK_plateau_pos : 0 < K_plateau)
    (h_plateau_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma_at_T ε - Real.rpow rho ((1 : ℝ) / L)|
          ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |(sigma_at_T ε) ^ L - rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry

/-! ## §2. Corrected qualitative convergence -/

/--
**Corrected qualitative plateau (Saxe-form convention).**

Under the Saxe-form Bernoulli ODE
  `σ̇(t) = L · μ · σ(t)^{2-1/L} · (ρ − σ(t)^L)`
with `σ(t) ∈ (0, ρ^{1/L})` for all t ≥ 0 and σ continuous, the diagonal
amplitude converges to `ρ^{1/L}` (NOT `ρ^L` as the inverted-form version
in `SignedODE.sigma_positive_branch_converges` claims).

**Proof strategy** — mirrors the original Aristotle proof (job `22e700ca`)
but with the corrected plateau:
  1. σ is monotone non-decreasing on `[0, ∞)` (the ODE RHS is positive on
     `(0, ρ^{1/L})`).
  2. σ bounded above by ρ^{1/L}, hence by `tendsto_atTop_ciSup` (applied to
     the monotone restriction) σ converges to its supremum `σ_∞`.
  3. If `σ_∞ < ρ^{1/L}`, then the ODE RHS at `σ_∞` is
     `L μ σ_∞^{2-1/L} (ρ − σ_∞^L) > 0` since `σ_∞^L < ρ`. By continuity of
     the RHS, σ̇ is bounded below by a positive constant on a neighborhood
     of `σ_∞`, contradicting σ being bounded above.
  4. Hence `σ_∞ = ρ^{1/L}`, and `σ → ρ^{1/L}`.

The proof in `SignedODE.sigma_positive_branch_converges` should transfer
with the bracket-form swap; the structure is identical.
-/
theorem sigma_positive_branch_converges_corrected
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlam_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_below : ∀ t : ℝ, 0 ≤ t →
        sigma t < Real.rpow (lambda / mu) ((1 : ℝ) / L))
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        ((L : ℝ) * mu * Real.rpow (sigma t) (2 - 1 / (L : ℝ))
          * (lambda / mu - (sigma t) ^ L)) t) :
    Filter.Tendsto sigma Filter.atTop
      (nhds (Real.rpow (lambda / mu) ((1 : ℝ) / L))) := by
  sorry

/-! ## §3. Corrected quantitative magnitude plateau bridge -/

/--
**Corrected Theorem 5.1′ bridge (Saxe-form convention).**

Under the Saxe-form ODE with init `σ(ε, 0) ≤ ε` and bound
`σ(ε, t) ∈ (0, (λ/μ)^{1/L})` for ε ∈ (0,1), there exists a
trajectory-derived observation time `T(ε)` at which

    `|σ(ε, T(ε)) − (λ/μ)^{1/L}| ≤ K_plateau · ε^{1/L} · |log ε|`.

**Proof strategy** — mirror Aristotle job `113fdc42` (the inverted-form
version):
  1. Apply qualitative `sigma_positive_branch_converges_corrected` to
     each ε-slice to get convergence to `(λ/μ)^{1/L}`.
  2. Use `Metric.tendsto_atTop` to extract, for each ε, an observation
     time `T(ε)` at which the plateau gap is below
     `ε^{1/L} · |log ε|`.
  3. Bundle via `Classical.choice` into a single function `T : ℝ → ℝ`
     and constant `K_plateau = 1`.

This is the cleanest path; it does NOT do the full Lyapunov + Grönwall
contraction analysis (the original session-88 attempt also skipped this
in favour of the qualitative + Metric.tendsto + Classical.choice route).
-/
theorem signed_recovery_pos_magnitude_plateau_corrected
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_below : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t →
        sigma ε t < Real.rpow (lambda / mu) ((1 : ℝ) / L))
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        ((L : ℝ) * mu * Real.rpow (sigma ε t) (2 - 1 / (L : ℝ))
          * (lambda / mu - (sigma ε t) ^ L)) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 ≤ ε) :
    ∃ T : ℝ → ℝ, ∃ K_plateau : ℝ, 0 < K_plateau ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma ε (T ε) - Real.rpow (lambda / mu) ((1 : ℝ) / L)|
          ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
  sorry

end JepaRhoRecovery
