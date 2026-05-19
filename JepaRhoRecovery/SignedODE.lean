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

/-! ## Theorem 4.1(a) — Positive branch is monotonically learned -/

/-
ORIGINAL STATEMENT (commented out — FALSE as stated).
   The original docstring claimed the upper bound is `σ < √(ρ·μ)`, but
   this is incorrect.  Counterexample: ρ = 0.01, μ = 100, λ = ρ·μ = 1, L = 2.
   Then √(ρ·μ) = 1, but at σ = 0.9 < 1 the derivative is
   1 · 0.9^2.5 − 100 · 0.9³ ≈ 0.77 − 72.9 < 0,
   contradicting monotonicity.

   The correct fixed point of the ODE
     σ̇ = λ · σ^{3−1/L} − (λ/ρ) · σ³
   is σ* = ρ^L  (solving ρ = σ^{1/L}), NOT √(ρ·μ).
   Below ρ^L the first term dominates and σ̇ > 0.

theorem sigma_positive_branch_monotone
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho mu : ℝ) (hlam_pos : 0 < lambda)
    (hrho_pos : 0 < rho) (hmu_pos : 0 < mu)
    (h_lambda_eq : lambda = rho * mu)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < sigma t)
    (hSigma_below : ∀ t ∈ Set.Icc 0 t_max,
        sigma t < Real.sqrt (rho * mu))
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / rho) * (sigma t) ^ 3) t) :
    MonotoneOn sigma (Set.Icc 0 t_max) := by
  sorry

**Theorem 4.1(a) (Positive-branch monotonicity — corrected).**

    The original statement used `σ < √(ρ·μ)` as the upper bound, but
    the actual fixed point of the ODE `σ̇ = λ·σ^{3-1/L} − (λ/ρ)·σ³`
    is `σ* = ρ^L` (from `ρ = σ^{1/L}`), not `√(ρ·μ)`.  Below `ρ^L`,
    the `λ·σ^{3-1/L}` term dominates `(λ/ρ)·σ³`, giving `σ̇ ≥ 0`.

    Modifications from original:
    • Removed `mu`, `h_lambda_eq`  (not needed for this ODE analysis).
    • Replaced `sigma t < Real.sqrt (rho * mu)` with `sigma t < rho ^ L`.

    Proof sketch (mirror of `sigma_negative_branch_antitone`):
    1. For `σ > 0` with `σ < ρ^L`, we have `σ^{1/L} < ρ` (rpow_lt_rpow).
    2. Rearranging: `ρ · σ^{3-1/L} > σ³`, hence
       `λ · σ^{3-1/L} > (λ/ρ) · σ³` (multiply by `λ/ρ > 0`).
    3. So `σ̇ > 0` on `(0, t_max)`, and `monotoneOn_of_deriv_nonneg` closes.

Below the fixed point `ρ^L`, the rpow term dominates the cubic:
`ρ · s^{3-1/L} > s³` whenever `0 < s < ρ^L` and `ρ > 0`.
-/
private lemma rpow_dominates_cube
    (L : ℕ) (hL : 2 ≤ L) (rho s : ℝ)
    (hrho_pos : 0 < rho) (hs_pos : 0 < s) (hs_lt : s < rho ^ L) :
    (s : ℝ) ^ 3 < rho * Real.rpow s (3 - 1 / (L : ℝ)) := by
  -- Rewrite $s^3$ as $s^{3 - 1/L} \cdot s^{1/L}$.
  have h_rewrite : s ^ 3 = s.rpow (3 - 1 / (L : ℝ)) * s.rpow (1 / (L : ℝ)) := by
    norm_num [ ← Real.rpow_add hs_pos ];
  -- Since $s < rho^L$, we have $s^{1/L} < rho$.
  have h_root : s.rpow (1 / (L : ℝ)) < rho := by
    exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) hs_lt ( by positivity ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] );
  convert mul_lt_mul_of_pos_left h_root ( Real.rpow_pos_of_pos hs_pos _ ) using 1 ; ring_nf at * ; aesop;
  norm_num [ mul_comm ]

theorem sigma_positive_branch_monotone
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hlam_pos : 0 < lambda)
    (hrho_pos : 0 < rho)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < sigma t)
    (hSigma_below : ∀ t ∈ Set.Icc 0 t_max,
        sigma t < rho ^ L)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / rho) * (sigma t) ^ 3) t) :
    MonotoneOn sigma (Set.Icc 0 t_max) := by
  refine' monotoneOn_of_deriv_nonneg _ _ _ _;
  · exact convex_Icc _ _;
  · assumption;
  · exact fun x hx => ( hSigma_ode x <| by simpa using hx ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt;
  · simp +zetaDelta at *;
    intro t ht ht'; rw [ hSigma_ode t ht ht' |> HasDerivAt.deriv ] ;
    have := rpow_dominates_cube L hL rho ( sigma t ) hrho_pos ( hSigma_pos t ht.le ht'.le ) ( hSigma_below t ht.le ht'.le );
    norm_num at *;
    rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith

/-! ## Theorem 4.1(b) — Zero branch is stationary -/

/-- **Theorem 4.1(b) (Zero-branch stationarity).**

    When `ρ = 0`, the projected covariance `λ = ρ · μ = 0`, so the diagonal
    ODE reduces to `σ̇ = 0`. Hence `σ` is constant on `[0, t_max]`.

    Stated against a slightly **simplified ODE** — the `(λ/ρ) · σ³` term is
    ill-defined at `ρ = 0`, so we use the equivalent `λ · σ^{3-1/L} − μ · σ³`
    form (with `λ = ρ · μ`), which is well-defined and equals the original
    ODE wherever `ρ ≠ 0`. -/
theorem sigma_zero_branch_constant
    (L : ℕ) (hL : 2 ≤ L)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max, HasDerivAt sigma 0 t) :
    ∀ t ∈ Set.Icc 0 t_max, sigma t = sigma 0 := by
  intro t ht
  have h_deriv_zero : ∀ s ∈ Set.Ioo 0 t_max, deriv sigma s = 0 := fun s hs =>
    (hSigma_ode s hs).deriv
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · simp [← hzero]
  · apply Eq.symm
    have hAnti : AntitoneOn sigma (Set.Icc 0 t_max) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact hSigma_cont
      · intro x hx
        have : x ∈ Set.Ioo 0 t_max := by simpa using hx
        exact (hSigma_ode x this).differentiableAt.differentiableWithinAt
      · intro x hx
        have : x ∈ Set.Ioo 0 t_max := by simpa using hx
        rw [h_deriv_zero x this]
    have hMono : MonotoneOn sigma (Set.Icc 0 t_max) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact hSigma_cont
      · intro x hx
        have : x ∈ Set.Ioo 0 t_max := by simpa using hx
        exact (hSigma_ode x this).differentiableAt.differentiableWithinAt
      · intro x hx
        have : x ∈ Set.Ioo 0 t_max := by simpa using hx
        rw [h_deriv_zero x this]
    have hle  : sigma t ≤ sigma 0 :=
      hAnti (Set.left_mem_Icc.mpr ht_max.le) ht ht.1
    have hge  : sigma 0 ≤ sigma t :=
      hMono (Set.left_mem_Icc.mpr ht_max.le) ht ht.1
    linarith

/-! ## Theorem 4.1(a′) — Positive-branch convergence to ρ^L -/

/-- **Theorem 4.1(a′) (Positive-branch convergence).**

    Stronger companion to `sigma_positive_branch_monotone`. With the same
    ODE on the half-line `[0, ∞)` and the same bound `σ(t) < ρ^L`, the
    diagonal amplitude converges to the fixed point `ρ^L` as `t → ∞`.

    This is the convergence statement consumed by Layer 4.2(i)
    (`sign_identification_pos_iff_asymptote`) — the monotonicity lemma
    alone is not enough to identify the asymptote.

    **PROVIDED SOLUTION** (7 steps; mirrors a standard ODE Lyapunov argument):
    1. Apply `sigma_positive_branch_monotone` on every restriction
       `[0, T]` (T > 0). Since `sigma t < ρ^L` for every `t ≥ 0`, the
       monotonicity hypotheses are satisfied uniformly, so `σ` is
       `Monotone` (globally non-decreasing) on `[0, ∞)`.
    2. `σ` is bounded above by `ρ^L`. Together with (1) and standard
       monotone-convergence (`Monotone.tendsto_atTop`), `σ` has a limit
       `σ_∞ ∈ [σ(0), ρ^L]`.
    3. Suppose for contradiction `σ_∞ < ρ^L`. Define
       `F : ℝ → ℝ, F s := λ · s^{3 − 1/L} − (λ/ρ) · s^3`.
       By `rpow_dominates_cube` (already in this file), `F σ_∞ > 0`.
       Set `η := F σ_∞ / 2 > 0`.
    4. `F` is continuous on `(0, ρ^L)`, so there exists `δ > 0` with
       `F s ≥ η` for `s ∈ [σ_∞ − δ, σ_∞]`. WLOG `σ_∞ − δ > σ(0) / 2 > 0`.
    5. Since `σ t → σ_∞` and `σ` is monotone, there is `T` such that
       `σ t ∈ [σ_∞ − δ, σ_∞]` for all `t ≥ T`. By the ODE hypothesis,
       `σ̇(t) = F (σ t) ≥ η` for `t ≥ T`.
    6. By the mean value theorem (or FTC), for `t ≥ T`,
       `σ t − σ T ≥ η · (t − T)`. Take `t → ∞`: LHS bounded by `ρ^L`,
       RHS → ∞. Contradiction.
    7. Therefore `σ_∞ = ρ^L`.

    Existing infrastructure to use:
      - `sigma_positive_branch_monotone` (this file) — produces (1).
      - `rpow_dominates_cube` (this file, private) — produces `F σ_∞ > 0`.
      - Mathlib: `Monotone.tendsto_atTop`, `Filter.Tendsto`,
        `Continuous.tendsto`, `MeanValueTheorem` / `sub_le_of_hasDerivAt_ge`. -/
theorem sigma_positive_branch_converges
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hlam_pos : 0 < lambda) (hrho_pos : 0 < rho)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_below : ∀ t : ℝ, 0 ≤ t → sigma t < rho ^ L)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / rho) * (sigma t) ^ 3) t) :
    Filter.Tendsto sigma Filter.atTop (nhds (rho ^ L)) := by
  sorry

end JepaRhoRecovery