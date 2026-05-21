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

/-
σ is monotone on [0, ∞): follows from sigma_positive_branch_monotone on each [0,T].
-/
private lemma sigma_pos_monotoneOn_Ici
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
    MonotoneOn sigma (Set.Ici 0) := by
  -- For any t₁, t₂ ∈ [0, ∞) with t₁ ≤ t₂, apply sigma_positive_branch_monotone on [0, t₂] (taking t_max = t₂). Need to handle t₂ = 0 separately (trivially). For t₂ > 0: hSigma_pos gives positivity on [0, t₂], hSigma_below gives the upper bound, hSigma_cont.continuousOn gives continuity, and hSigma_ode restricted to (0, t₂) gives the ODE. Then MonotoneOn [0, t₂] applied to t₁, t₂ gives σ(t₁) ≤ σ(t₂).
  intros t₁ ht₁ t₂ ht₂ ht₁t₂
  by_cases ht₂_zero : t₂ = 0;
  · grind;
  · have := sigma_positive_branch_monotone L hL lambda rho hlam_pos hrho_pos t₂ ( lt_of_le_of_ne ht₂ ( Ne.symm ht₂_zero ) ) sigma ( fun t ht => hSigma_pos t ht.1 ) ( fun t ht => hSigma_below t ht.1 ) ( hSigma_cont.continuousOn ) ( fun t ht => hSigma_ode t ht.1 );
    exact this ⟨ ht₁, ht₁t₂ ⟩ ⟨ ht₂, le_rfl ⟩ ht₁t₂

/-
The ODE RHS F(s) = λ·s^{3-1/L} - (λ/ρ)·s³ is strictly positive for s ∈ (0, ρ^L).
    Follows from rpow_dominates_cube.
-/
private lemma ode_rhs_pos_below_fixed_point
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho s : ℝ) (hlam_pos : 0 < lambda) (hrho_pos : 0 < rho)
    (hs_pos : 0 < s) (hs_lt : s < rho ^ L) :
    0 < lambda * Real.rpow s (3 - 1 / (L : ℝ)) - (lambda / rho) * s ^ 3 := by
  -- We can divide both sides by `lambda` since it is positive.
  suffices h_div_lambda : 0 < s.rpow (3 - 1 / (L : ℝ)) - (1 / rho) * s ^ 3 by
    convert mul_pos hlam_pos h_div_lambda using 1 ; ring;
  -- We can divide both sides by `s^3` since it is positive.
  suffices h_div_s3 : 0 < s.rpow (3 - 1 / (L : ℝ) - 3) - (1 / rho) by
    convert mul_pos h_div_s3 ( pow_pos hs_pos 3 ) using 1 ; norm_num [ Real.rpow_sub hs_pos ] ; ring;
    rw [ Real.rpow_neg hs_pos.le ] ; ring;
  norm_num [ Real.rpow_neg hs_pos.le ];
  gcongr;
  exact lt_of_lt_of_le ( Real.rpow_lt_rpow hs_pos.le hs_lt ( by positivity ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ] )

/-- **Theorem 4.1(a′) (Positive-branch convergence).**

    Stronger companion to `sigma_positive_branch_monotone`. With the same
    ODE on the half-line `[0, ∞)` and the same bound `σ(t) < ρ^L`, the
    diagonal amplitude converges to the fixed point `ρ^L` as `t → ∞`.

    This is the convergence statement consumed by Layer 4.2(i)
    (`sign_identification_pos_iff_asymptote`) — the monotonicity lemma
    alone is not enough to identify the asymptote.

    Proved by Aristotle job `22e700ca` (session 77): supremum via
    `tendsto_atTop_ciSup` on `t ↦ σ(max t 0)`; if `σ_∞ < ρ^L`, MVT +
    `ode_rhs_pos_below_fixed_point` (wrapping `rpow_dominates_cube`)
    gives a positive lower bound on the derivative, contradicting
    boundedness. -/
-- ⚠ DEPRECATED (session 90, 2026-05-21). Plateau target `ρ^L` + ODE bracket
--   `(1 − σ^(1/L)/ρ)` are the inverted form. Correct version is
--   `Corrected.sigma_positive_branch_converges_corrected` (plateau `ρ^(1/L)`,
--   bracket `(ρ − σ^L)`, Saxe form). Self-consistent under inverted hypotheses;
--   preserved as historical record.
@[deprecated "Inverted ODE form; use Corrected.sigma_positive_branch_converges_corrected"]
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
  -- Apply the fact that the supremum of the range of sigma is rho^L.
  have h_sup_eq : iSup (fun t => sigma (max t 0)) = rho ^ L := by
    by_contra h_contra;
    -- Since $\sigma$ is monotone and bounded above, it converges to some limit $\sigma_\infty$.
    obtain ⟨sigma_inf, hsigma_inf⟩ : ∃ sigma_inf, Filter.Tendsto sigma Filter.atTop (nhds sigma_inf) ∧ sigma_inf < rho ^ L := by
      have h_sigma_inf_lt : Filter.Tendsto sigma Filter.atTop (nhds (iSup (fun t => sigma (max t 0)))) := by
        have h_sigma_inf_lt : Filter.Tendsto (fun t => sigma (max t 0)) Filter.atTop (nhds (iSup (fun t => sigma (max t 0)))) := by
          apply_rules [ tendsto_atTop_ciSup ];
          · have := sigma_pos_monotoneOn_Ici L hL lambda rho hlam_pos hrho_pos sigma hSigma_pos hSigma_below hSigma_cont hSigma_ode;
            exact fun x y hxy => this ( show 0 ≤ Max.max x 0 by positivity ) ( show 0 ≤ Max.max y 0 by positivity ) ( max_le_max hxy le_rfl );
          · exact ⟨ rho ^ L, Set.forall_mem_range.mpr fun t => le_of_lt ( hSigma_below _ ( le_max_right _ _ ) ) ⟩;
        exact h_sigma_inf_lt.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht; simp +decide [ ht ] );
      exact ⟨ _, h_sigma_inf_lt, lt_of_le_of_ne ( le_of_tendsto_of_tendsto h_sigma_inf_lt tendsto_const_nhds <| Filter.eventually_atTop.mpr ⟨ 0, fun t ht => le_of_lt <| hSigma_below t <| by positivity ⟩ ) h_contra ⟩;
    -- Since $\sigma$ is monotone and bounded above, it converges to some limit $\sigma_\infty$. By the properties of the ODE, we have $\sigma_\infty = \rho^L$.
    have h_sigma_inf_eq : Filter.Tendsto (fun t => (sigma (t + 1) - sigma t) / 1) Filter.atTop (nhds (lambda * sigma_inf ^ (3 - 1 / (L : ℝ)) - (lambda / rho) * sigma_inf ^ 3)) := by
      have h_sigma_inf_eq : Filter.Tendsto (fun t => deriv sigma t) Filter.atTop (nhds (lambda * sigma_inf ^ (3 - 1 / (L : ℝ)) - (lambda / rho) * sigma_inf ^ 3)) := by
        have h_sigma_inf_eq : Filter.Tendsto (fun t => lambda * (sigma t) ^ (3 - 1 / (L : ℝ)) - (lambda / rho) * (sigma t) ^ 3) Filter.atTop (nhds (lambda * sigma_inf ^ (3 - 1 / (L : ℝ)) - (lambda / rho) * sigma_inf ^ 3)) := by
          exact Filter.Tendsto.sub ( tendsto_const_nhds.mul ( hsigma_inf.1.rpow_const <| Or.inr <| by linarith [ show ( 1 : ℝ ) / L ≤ 1 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ] ) ) ( tendsto_const_nhds.mul ( hsigma_inf.1.pow 3 ) );
        exact h_sigma_inf_eq.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ hSigma_ode t ht |> HasDerivAt.deriv ] ; norm_num );
      have h_mean_value : ∀ t > 0, ∃ c ∈ Set.Ioo t (t + 1), deriv sigma c = (sigma (t + 1) - sigma t) / 1 := by
        intro t ht; have := exists_deriv_eq_slope sigma ( show t < t + 1 by linarith ) ; norm_num at *;
        exact this ( hSigma_cont.continuousOn ) ( fun x hx => ( hSigma_ode x ( by linarith [ hx.1 ] ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt ) );
      rw [ Metric.tendsto_nhds ] at *;
      intro ε hε; rcases Filter.eventually_atTop.mp ( h_sigma_inf_eq ε hε ) with ⟨ M, hM ⟩ ; filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop M ] with t ht₁ ht₂; obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value t ht₁; exact hc₂ ▸ hM c ( by linarith [ hc₁.1 ] ) ;
    have := h_sigma_inf_eq.sub ( hsigma_inf.1.comp ( show Filter.Tendsto ( fun t : ℝ => t + 1 ) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_add tendsto_const_nhds ) |> Filter.Tendsto.sub <| hsigma_inf.1 ) ; norm_num at this;
    -- Since $\sigma_\infty < \rho^L$, we have $\sigma_\infty^{1/L} < \rho$.
    have h_sigma_inf_lt_rho : sigma_inf ^ (1 / (L : ℝ)) < rho := by
      exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( show 0 ≤ sigma_inf from le_of_tendsto_of_tendsto tendsto_const_nhds hsigma_inf.1 <| Filter.eventually_atTop.mpr ⟨ 0, fun t ht => le_of_lt <| hSigma_pos t ht ⟩ ) hsigma_inf.2 <| by positivity ) <| by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ;
    -- Since $\sigma_\infty < \rho^L$, we have $\sigma_\infty^{3 - 1/L} > \sigma_\infty^3 / \rho$.
    have h_sigma_inf_gt : sigma_inf ^ (3 - 1 / (L : ℝ)) > sigma_inf ^ 3 / rho := by
      have h_sigma_inf_gt : sigma_inf ^ (3 - 1 / (L : ℝ)) = sigma_inf ^ 3 / sigma_inf ^ (1 / (L : ℝ)) := by
        rw [ Real.rpow_sub ] <;> norm_num;
        exact lt_of_lt_of_le ( hSigma_pos 0 le_rfl ) ( le_of_tendsto_of_tendsto tendsto_const_nhds hsigma_inf.1 ( Filter.eventually_atTop.mpr ⟨ 0, fun t ht => by exact ( show sigma t ≥ sigma 0 from by exact ( sigma_pos_monotoneOn_Ici L hL lambda rho hlam_pos hrho_pos sigma ( fun t ht => hSigma_pos t ht ) ( fun t ht => hSigma_below t ht ) hSigma_cont ( fun t ht => hSigma_ode t ht ) ) ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ( by linarith ) ) ⟩ ) );
      rw [h_sigma_inf_gt];
      gcongr;
      · exact pow_pos ( lt_of_lt_of_le ( hSigma_pos 0 le_rfl ) ( le_of_tendsto_of_tendsto tendsto_const_nhds hsigma_inf.1 ( Filter.eventually_atTop.mpr ⟨ 0, fun t ht => by exact ( show sigma t ≥ sigma 0 from by exact ( sigma_pos_monotoneOn_Ici L hL lambda rho hlam_pos hrho_pos sigma hSigma_pos hSigma_below hSigma_cont hSigma_ode ) ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht ) ⟩ ) ) ) _;
      · exact Real.rpow_pos_of_pos ( lt_of_lt_of_le ( hSigma_pos 0 le_rfl ) ( le_of_tendsto_of_tendsto tendsto_const_nhds hsigma_inf.1 ( Filter.eventually_atTop.mpr ⟨ 0, fun t ht => by exact ( show sigma t ≥ sigma 0 from by exact ( sigma_pos_monotoneOn_Ici L hL lambda rho hlam_pos hrho_pos sigma ( fun t ht => hSigma_pos t ht ) ( fun t ht => hSigma_below t ht ) hSigma_cont ( fun t ht => hSigma_ode t ht ) ) ( Set.self_mem_Ici ) ( Set.mem_Ici.mpr ht ) ( by linarith ) ) ⟩ ) ) ) _;
    ring_nf at *; nlinarith;
  rw [ ← h_sup_eq ];
  have h_sigma_conv : Filter.Tendsto (fun t => sigma (max t 0)) Filter.atTop (nhds (⨆ t, sigma (max t 0))) := by
    apply_rules [ tendsto_atTop_ciSup ];
    · have := sigma_pos_monotoneOn_Ici L hL lambda rho hlam_pos hrho_pos sigma hSigma_pos hSigma_below hSigma_cont hSigma_ode;
      exact fun x y hxy => this ( show 0 ≤ Max.max x 0 by positivity ) ( show 0 ≤ Max.max y 0 by positivity ) ( max_le_max hxy le_rfl );
    · exact ⟨ rho ^ L, Set.forall_mem_range.mpr fun t => le_of_lt ( hSigma_below _ ( le_max_right _ _ ) ) ⟩;
  exact h_sigma_conv.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht; rw [ max_eq_left ht ] )

end JepaRhoRecovery