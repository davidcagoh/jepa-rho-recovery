/-
# JepaRhoRecovery.SignedODE

Layer 4.1 — signed-ρ ODE analysis. This file targets the **negative branch**:
when ρ_r* < 0, the diagonal amplitude σ_r is actively suppressed. This is the
new physics that Littwin 2024 / paper 1 both exclude.

The full Layer 4.1 trichotomy (positive / zero / negative) is split across
three follow-up jobs:

  * Positive branch: inherits from paper 1 (`bernoulli_laurent_bound`); will be
    ported in a separate dispatch.
  * Zero branch: trivial (ODE degenerates to σ̇ = 0); will be added when
    Layer 2.1 lands the diagonal ODE in its zero-coefficient form.
  * Negative branch: **this file**.

Signed-first discipline: `lambda`, `rho` are real-valued; sign is asserted via
strict inequalities, never baked into types.

The diagonal ODE used here is the one stated in the roadmap (Gap 2.1):

    σ̇_r(t) = λ_r* · σ_r(t)^{3 - 1/L} − (λ_r* / ρ_r*) · σ_r(t)^3.

Layer 2.1 will derive this from the gradient flow + biorthogonality; here we
take it as a `HasDerivAt` hypothesis, mirroring how paper-1 handles
`bernoulli_laurent_bound` upstream of `quasiStatic_approx`.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

set_option maxHeartbeats 400000

open Real Filter
open scoped Matrix

namespace JepaRhoRecovery

/-! ## Theorem 4.1(c) — Negative branch is monotonically suppressed -/

/-- **Theorem 4.1(c) (Negative-branch suppression — monotonicity).**

    Let `L ≥ 2`, and let `λ < 0`, `ρ < 0` be the signed projected covariance
    and generalised eigenvalue for some negative-ρ feature. Suppose
    `σ : ℝ → ℝ` is a positive trajectory satisfying the generalised diagonal
    ODE on `(0, t_max)`:

        σ̇(t) = λ · σ(t)^{3 − 1/L} − (λ/ρ) · σ(t)^3.

    Then `σ` is monotonically non-increasing on `[0, t_max]`.

    This is the new physics: when ρ < 0, both terms of the diagonal ODE are
    negative for `σ > 0`, so the encoder amplitude is actively suppressed.
    Contrast with paper 1, which assumes `ρ > 0` throughout and proves
    convergence to a strictly positive fixed point.

    PROVIDED SOLUTION
    Step 1 (sign of each term). For every `t ∈ (0, t_max)` with `σ t > 0`:
      * `λ · σ(t)^{3 − 1/L} < 0`, since `λ < 0` and `σ(t)^{3 − 1/L}
        = Real.rpow (σ t) (3 − 1/L) > 0` (positive base, real exponent).
      * `−(λ/ρ) · σ(t)^3 < 0`, since `λ < 0` and `ρ < 0` give `λ/ρ > 0`,
        and `σ(t)^3 > 0`.
    Step 2 (derivative is negative). Adding the two strictly-negative terms
    gives `HasDerivAt σ (σ' t) t` with `σ' t < 0` for all `t ∈ (0, t_max)`.
    Use `hSigma_ode` to extract the explicit derivative and `nlinarith` /
    `positivity` to combine the two sign facts.
    Step 3 (monotonicity from negative derivative). Apply
    `antitoneOn_of_hasDerivWithinAt_nonpos` (Mathlib) to the closed interval
    `[0, t_max]`:
      * `ContinuousOn σ (Set.Icc 0 t_max)` is supplied by `hSigma_cont`.
      * For every interior point `t ∈ Set.Ioo 0 t_max`,
        `HasDerivWithinAt σ (σ' t) (interior (Set.Icc 0 t_max)) t` follows
        from `hSigma_ode t ht |>.hasDerivWithinAt` (or
        `HasDerivAt.hasDerivWithinAt`).
      * `σ' t ≤ 0` is the conclusion of Step 2 (strict inequality, weakened).
    The resulting `AntitoneOn` statement is exactly the goal.
-/
theorem sigma_negative_branch_antitone
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hlam_neg : lambda < 0) (hrho_neg : rho < 0)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < sigma t)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / rho) * (sigma t) ^ 3) t) :
    AntitoneOn sigma (Set.Icc 0 t_max) := by
  have h_deriv_neg : ∀ t ∈ Set.Ioo 0 t_max, deriv sigma t ≤ 0 := by
    intro t ht; have := hSigma_ode t ht; have := this.deriv; simp_all +decide [ ne_of_gt, division_def ] ;
    nlinarith [ show 0 < sigma t ^ ( 3 - ( L : ℝ ) ⁻¹ ) by exact Real.rpow_pos_of_pos ( hSigma_pos t ht.1.le ht.2.le ) _, show 0 < sigma t ^ 3 by exact pow_pos ( hSigma_pos t ht.1.le ht.2.le ) _, show lambda * rho⁻¹ > 0 by nlinarith [ mul_inv_cancel₀ ( ne_of_lt hrho_neg ) ] ];
  apply_rules [ antitoneOn_of_deriv_nonpos ];
  · exact convex_Icc _ _;
  · exact fun x hx => ( hSigma_ode x <| by simpa using hx ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt;
  · aesop

/-! ## Theorem 4.1(c) — Quantitative suppression bound (corollary)

    Once monotonicity is in hand, the suppression timescale follows from the
    dominant `λ σ^{3-1/L}` term. The roadmap claims
    `t_r^† = O(|λ_r*|^{-1} ε^{1/L - 2})`; we state the weaker but cleaner
    *upper bound on σ at the suppression time* form here. This is a
    follow-up corollary; not part of the Layer 4.1 minimum.
-/

/-- **Corollary 4.1(c′) (Suppression upper bound).**

    Under the hypotheses of `sigma_negative_branch_antitone`, the trajectory
    stays below its initial value:
        σ(t) ≤ σ(0) for all t ∈ [0, t_max].

    PROVIDED SOLUTION
    Direct from `sigma_negative_branch_antitone` applied to the pair
    `(0, t)` with `0 ≤ 0 ≤ t ≤ t_max`. -/
theorem sigma_negative_branch_le_init
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hlam_neg : lambda < 0) (hrho_neg : rho < 0)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < sigma t)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / rho) * (sigma t) ^ 3) t) :
    ∀ t ∈ Set.Icc 0 t_max, sigma t ≤ sigma 0 := by
  intro t ht
  exact sigma_negative_branch_antitone L hL lambda rho hlam_neg hrho_neg
    t_max ht_max sigma hSigma_pos hSigma_cont hSigma_ode
    (Set.left_mem_Icc.mpr ht_max.le) ht ht.1

end JepaRhoRecovery
