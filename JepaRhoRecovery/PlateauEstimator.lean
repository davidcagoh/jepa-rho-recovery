/-
# JepaRhoRecovery.PlateauEstimator

Layer 2.2′ — **plateau-based and early-slope-based identifiability** for the
positive branch. These two abstract analytic lemmas underpin the
pure-trajectory recovery story (paper §5 Thm 5.1′ and Thm 5.2).

## Two estimators, one trajectory

The diagonal Bernoulli ODE
    σ̇_r = λ_r* · σ_r^{3-1/L} - μ_r · σ_r^3
has two free parameters (λ_r*, μ_r) and the positive-branch trajectory
exposes them through two STRUCTURALLY INDEPENDENT observables:

  * **Plateau** σ_r^∞ = (ρ_r*)^L (set σ̇ = 0 ⇒ σ_r^{1/L} = λ_r*/μ_r = ρ_r*).
    Identifies the RATIO ρ_r* = λ_r*/μ_r alone, **without separate
    knowledge of λ_r* or μ_r**, hence WITHOUT covariance side-channel.
  * **Early-time slope.** For σ_r ≪ 1, the σ_r^3 term is dominated by
    σ_r^{3-1/L} by factor σ_r^{-1/L} ≥ ε^{-1/L}. So σ̇_r ≈ λ_r* σ_r^{3-1/L},
    which integrates explicitly. Identifies λ_r* ALONE (μ_r absent at
    leading order).

Combining the two recovers (λ_r*, μ_r) jointly from one trajectory.

## File contents

  * `rho_hat_plateau_rate` — given a plateau-approach hypothesis
    `|σ(T(ε)) - ρ^L| ≤ K · ε^{1/L} · |log ε|`, the plateau estimator
    `σ(T)^{1/L}` recovers `ρ` at rate O(ε^{1/L} |log ε|).
    Aristotle job `25ff1480` (session 86, landed clean).
  * `lambda_hat_early_slope_rate` — given the early-time σ-bound
    `|σ(t₀) - σ_idealised(t₀)| ≤ K · ε^{(L+1)/L} · |log ε|` for σ_idealised
    solving the μ = 0 ODE, the slope estimator
    `λ̂(ε) := (L/(2L-1)) · (ε^{-(2L-1)/L} - σ(t₀)^{-(2L-1)/L}) / t₀`
    recovers `λ` at rate O(ε^{1/L} |log ε|).
    Aristotle job `95ddb6a0` (session 86). **Hypothesis exponent corrected
    from ε^{1/L} to ε^{(L+1)/L}**; original statement was false (Aristotle
    constructed an explicit counterexample at L=2 — see block comment in
    §5.2 below). Also added side condition `c·(2L−1)/L < 1` to keep the
    idealised σ positive (observation time before blow-up). Conclusion
    unchanged.

## Pattern

These follow `Inversion.rho_hat_rate`'s pattern: take the trajectory→Laurent
or trajectory→plateau bound as a HYPOTHESIS (proved separately by the
JEPA-dynamics chain in `SignedRecovery.lean` and the ODE bridges of
`SignedODE.lean`), and produce the estimator rate by a self-contained
analytic argument. The HARD ODE work is in the bridge lemmas; THIS file
is the Lipschitz/monotonicity/algebraic-reduction part.

## Vacuity discipline

Per `CLAUDE.md`:
  * `ε_0 > 0` and `C > 0` are forced existentials; vacuous `ε_0 = 0` or
    `C = 0` witnesses violate the contract.
  * Hypotheses `h_plateau_bound` / `h_early_slope_bound` MUST be used —
    proofs that ignore them are degenerate and rejected.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Finset Filter
open scoped Matrix

namespace JepaRhoRecovery

/-! ### Shared helper -/

/-
For any positive `K` and `δ`, the product `K * ε^(1/L) * |log ε|` is
eventually less than `δ` near `ε = 0⁺`.
-/
private lemma eps_rpow_log_eventually_small
    (L : ℕ) (hL : 2 ≤ L) (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∃ ε_0 : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε_0 →
        K * ε ^ ((1 : ℝ) / L) * |Real.log ε| < δ := by
  have h_tendsto : Filter.Tendsto (fun ε : ℝ => K * ε ^ ((1 : ℝ) / L) * |Real.log ε|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    suffices h_log : Filter.Tendsto (fun ε : ℝ => ε ^ ((1 : ℝ) / L) * (-Real.log ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
      simpa [ mul_assoc ] using h_log.const_mul K |> Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun x hx => by rw [ abs_of_neg ( Real.log_neg hx.1 hx.2 ) ] ; ring );
    suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (y / L) * (-y)) Filter.atBot (nhds 0) by
      have := h_log.comp Real.tendsto_log_nhdsNE_zero;
      refine' Filter.Tendsto.congr' _ ( this.mono_left <| nhdsWithin_mono _ <| by simp +decide );
      filter_upwards [ self_mem_nhdsWithin ] with x hx using by simp +decide [ Real.rpow_def_of_pos hx, div_eq_mul_inv, mul_comm ] ;
    suffices h_lim_z : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * L * z) Filter.atTop (nhds 0) by
      convert h_lim_z.comp ( Filter.tendsto_neg_atBot_atTop.comp <| Filter.tendsto_id.atBot_mul_const <| inv_pos.mpr <| Nat.cast_pos.mpr <| zero_lt_two.trans_le hL ) using 2 ; norm_num ; ring;
      norm_num [ show L ≠ 0 by positivity ];
    simpa [ mul_assoc, mul_comm, mul_left_comm ] using Filter.Tendsto.const_mul ( L : ℝ ) ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
  have := Metric.tendsto_nhdsWithin_nhds.mp h_tendsto δ hδ;
  obtain ⟨ ε_0, hε_0₁, hε_0₂ ⟩ := this; exact ⟨ Min.min ε_0 1 / 2, by positivity, by linarith [ min_le_left ε_0 1, min_le_right ε_0 1 ], fun ε hε₁ hε₂ => by linarith [ abs_lt.mp ( hε_0₂ hε₁ ( by rw [ dist_comm ] ; exact abs_lt.mpr ⟨ by linarith [ min_le_left ε_0 1, min_le_right ε_0 1 ], by linarith [ min_le_left ε_0 1, min_le_right ε_0 1 ] ⟩ ) ) ] ⟩ ;

/-! ### Helpers for `rho_hat_plateau_rate` -/

/-
Identity: `(rho ^ L) ^ ((1:ℝ)/L) = rho` for `rho > 0` and `L ≥ 1`.
-/
private lemma rpow_pow_inv_cancel (rho : ℝ) (L : ℕ) (hrho : 0 < rho) (hL : 1 ≤ L) :
    Real.rpow (rho ^ L) ((1 : ℝ) / L) = rho := by
  norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul hrho.le, mul_inv_cancel₀ ( by positivity : ( L : ℝ ) ≠ 0 ) ]

/-
Algebraic Lipschitz bound: for `σ > 0` and `ρ > 0`,
    `|σ^{1/L} - ρ| ≤ |σ - ρ^L| / ρ^{L-1}`.
    Uses the factorization `a^L - b^L = (a-b) Σ_{k} a^k b^{L-1-k}`
    and the lower bound `Σ ≥ b^{L-1}`.
-/
private lemma root_lipschitz_bound (sigma rho : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    |Real.rpow sigma ((1 : ℝ) / L) - rho|
      ≤ |sigma - rho ^ L| / rho ^ (L - 1) := by
  set a := sigma.rpow (1 / L : ℝ)
  set b := rho ^ (1 / L : ℝ)
  set b := rho
  have ha_pos : 0 < a := by
    exact Real.rpow_pos_of_pos hsigma _
  have hb_pos : 0 < b := by
    exact hrho;
  have h_sum : (∑ i ∈ Finset.range L, a ^ i * b ^ (L - 1 - i)) * (a - b) = a ^ L - b ^ L := by
    rw [ geom_sum₂_mul ];
  have h_abs : |a ^ L - b ^ L| = |sigma - rho ^ L| := by
    simp +zetaDelta at *;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ];
  have h_sum_ge : ∑ i ∈ Finset.range L, a ^ i * b ^ (L - 1 - i) ≥ b ^ (L - 1) := by
    exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun i _ => mul_nonneg ( pow_nonneg ha_pos.le i ) ( pow_nonneg hb_pos.le ( L - 1 - i ) ) ) ( Finset.mem_range.mpr hL ) );
  rw [ le_div_iff₀ ( pow_pos hb_pos _ ) ];
  cases abs_cases ( a - b ) <;> cases abs_cases ( a ^ L - b ^ L ) <;> nlinarith [ pow_pos hb_pos ( L - 1 ) ]

/-! ## §5.1′ — Plateau estimator (positive branch)

    From the convergence `σ_r(t) → (ρ_r*)^L` (proved sorry-free as
    `SignedODE.sigma_positive_branch_converges`, Aristotle `22e700ca`),
    upgraded to a quantitative rate of approach, the plateau estimator
    `σ_r(T)^{1/L}` recovers ρ_r* with no covariance input. -/

/-- **Theorem 5.1′ (Plateau estimator, abstract form).**

    Suppose `σ_at_T` is a function of `ε` representing the observed
    plateau value σ_r(T(ε)) at a sufficiently late time T(ε), and we
    have the plateau-approach bound

        |σ_at_T ε - ρ^L| ≤ K_plateau · ε^{1/L} · |log ε|     (∀ ε ∈ (0,1)).

    Then the **plateau estimator** `ρ̂_plateau(ε) := (σ_at_T ε)^{1/L}`
    satisfies

        |ρ̂_plateau ε - ρ| ≤ C · ε^{1/L} · |log ε|

    for all `ε ∈ (0, ε_0)`, with explicit positive ε_0, C depending on
    `L, ρ, K_plateau` only.

    **Proof strategy** (Aristotle `25ff1480`): algebraic factorisation
    `σ - ρ^L = (σ^{1/L} - ρ) · Σ_{k=0}^{L-1} (σ^{1/L})^k ρ^{L-1-k}`
    gives `|σ^{1/L} - ρ| ≤ |σ - ρ^L| / ρ^{L-1}` (the sum is ≥ ρ^{L-1}
    from the k=0 term alone). Multiply through by the plateau hypothesis.
    Constant `C = K_plateau / ρ^{L-1}`. -/
-- ⚠ DEPRECATED (session 90, 2026-05-21). Inverted-form plateau hypothesis
--   `|sigma_at_T ε - rho^L| ≤ ...`. Correct version is `Corrected.rho_hat_plateau_rate_corrected`
--   which uses plateau target `ρ^(1/L)` and estimator `σ^L`. This declaration
--   is algebraically consistent under its (inverted) hypotheses but disconnected
--   from JEPA dynamics. Preserved as historical record.
@[deprecated "Inverted ODE form; use Corrected.rho_hat_plateau_rate_corrected"]
theorem rho_hat_plateau_rate
    (L : ℕ) (hL : 2 ≤ L)
    (rho : ℝ) (hrho_pos : 0 < rho)
    (sigma_at_T : ℝ → ℝ)
    (K_plateau : ℝ) (hK_plateau_pos : 0 < K_plateau)
    (h_plateau_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma_at_T ε - rho ^ L| ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |Real.rpow (sigma_at_T ε) ((1 : ℝ) / L) - rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  obtain ⟨ε_0, hε0_pos, hε0_lt1, hε0_small⟩ :=
    eps_rpow_log_eventually_small L hL K_plateau (rho ^ L / 2) hK_plateau_pos (by positivity)
  refine ⟨ε_0, K_plateau / rho ^ (L - 1), hε0_pos, hε0_lt1, div_pos hK_plateau_pos (pow_pos hrho_pos _), ?_⟩
  intro ε hε_pos hε_lt_ε0
  have hε_lt1 : ε < 1 := hε_lt_ε0.trans hε0_lt1
  have h_bound := h_plateau_bound ε hε_pos hε_lt1
  have h_small := (hε0_small ε hε_pos hε_lt_ε0).le
  have hsigma_pos : 0 < sigma_at_T ε := by
    have h1 : sigma_at_T ε - rho ^ L ≥ -(rho ^ L / 2) := by
      have := abs_nonneg (sigma_at_T ε - rho ^ L)
      linarith [abs_le.mp (h_bound.trans h_small)]
    linarith [pow_pos hrho_pos L]
  have h_lip := root_lipschitz_bound (sigma_at_T ε) rho L (by linarith) hsigma_pos hrho_pos
  have h_rhoL_pos : (0 : ℝ) < rho ^ (L - 1) := pow_pos hrho_pos _
  calc |Real.rpow (sigma_at_T ε) ((1 : ℝ) / L) - rho|
      ≤ |sigma_at_T ε - rho ^ L| / rho ^ (L - 1) := h_lip
    _ ≤ (K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) / rho ^ (L - 1) :=
          div_le_div_of_nonneg_right h_bound h_rhoL_pos.le
    _ = K_plateau / rho ^ (L - 1) * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by ring

/-! ## §5.2 — Early-time slope estimator for λ_r* (positive branch)

    For ε small enough that `σ_r(t)` is much smaller than its plateau on
    `[0, t₀]`, the μ_r σ_r^3 term is dominated by λ_r* σ_r^{3-1/L}
    uniformly. Integrating `σ̇ = λ σ^{3-1/L}` from σ(0)=ε to σ(t₀):

        d/dt [-(L/(2L-1)) σ^{-(2L-1)/L}] = λ
      ⇒  σ(t₀)^{-(2L-1)/L} - ε^{-(2L-1)/L} = -((2L-1)/L) · λ · t₀
      ⇒  λ = (L/(2L-1)) · (ε^{-(2L-1)/L} - σ(t₀)^{-(2L-1)/L}) / t₀.

    The μ_r perturbation is controlled by Grönwall as an O(ε^{(L+1)/L})
    correction (the μ term contributes at most a factor 1+O(ε^{1/L})
    to the integral since σ ≤ a constant times ε on [0, t₀]). -/

/-! ### Counterexample to the original (ε^{1/L}) statement

    **The original statement of Theorem 5.2 (with hypothesis exponent
    `ε^{1/L}`) is FALSE.** Aristotle (job `95ddb6a0`) constructed the
    counterexample below before producing the corrected proof.

    Counterexample: Take L = 2, λ = 1, c = 0.3, K = 1.
    Then α = (2L-1)/L = 3/2 and σ_id(ε) = Aε where A = (1-cα)^{-1/α}
    = 0.55^{-2/3} ≈ 1.49. The hypothesis bound is K·ε^{1/2}·|log ε|.

    For small ε, the perturbation K·ε^{1/2}·|log ε| ≫ σ_id(ε) = Aε
    (since ε^{1/2} ≫ ε). This allows σ to deviate from σ_id by an
    amount much larger than σ_id itself. In particular, taking
    σ(ε) = σ_id(ε) + (K/2)·ε^{1/2}·|log ε| satisfies the bound and
    has σ(ε) ≈ (K/2)·ε^{1/2}·|log ε| for small ε.

    The estimator then gives:
    est ≈ (L/(2L-1)) · ε^{-α} / (c·λ⁻¹·ε^{-α}) = λ/(cα) ≈ 2.222 ≠ λ = 1.

    So |est - λ| → 1.222 > 0, while C·ε^{1/2}·|log ε| → 0.
    No finite C works for all small ε.

    **Root cause**: The hypothesis perturbation ε^{1/L} is too large
    relative to σ_id ≈ ε. The physically correct perturbation from the
    μ-term in the Bernoulli ODE is O(ε^{(L+1)/L}) by Grönwall analysis,
    which is ≪ ε for small ε.

    **Fix**: Change the hypothesis exponent from 1/L to (L+1)/L.
    Additionally, add `hc_small : c * ((2L-1)/L) < 1` to ensure σ_id > 0
    (i.e., the observation time is before blow-up). -/

/- Original (false) theorem — kept for reference:

theorem lambda_hat_early_slope_rate_ORIGINAL
    (L : ℕ) (hL : 2 ≤ L)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (sigma_at_t0 : ℝ → ℝ)
    (K_early : ℝ) (hK_early_pos : 0 < K_early)
    (h_early_slope_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        0 < sigma_at_t0 ε ∧
        |sigma_at_t0 ε
          - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / L)
                      - ((2 * (L : ℝ) - 1) / L) * lambda
                          * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L)))
                      (-L / (2 * (L : ℝ) - 1))|
          ≤ K_early * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |((L : ℝ) / (2 * (L : ℝ) - 1))
              * (ε ^ (-(2 * (L : ℝ) - 1) / L)
                  - Real.rpow (sigma_at_t0 ε) (-(2 * (L : ℝ) - 1) / L))
              / (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L))
           - lambda|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry
-/

/-! ### Helper lemmas for the corrected Theorem 5.2 -/

/-
Mean-value bound for `x ↦ x ^ (-α)` on a positive interval.
    For `x, y ≥ a > 0` and `α > 0`:
    `|x^{-α} - y^{-α}| ≤ α · a^{-α-1} · |x - y|`.
-/
private lemma rpow_neg_mvt_bound (α x y a : ℝ)
    (hα : 0 < α) (hx : 0 < x) (hy : 0 < y)
    (ha : 0 < a) (hxa : a ≤ x) (hya : a ≤ y) :
    |x ^ (-α) - y ^ (-α)| ≤ α * a ^ (-α - 1) * |x - y| := by
  have h_mean_value : ∀ x y : ℝ, 0 < x → 0 < y → x ≤ y → |x ^ (-α) - y ^ (-α)| ≤ α * x ^ (-α - 1) * |x - y| := by
    intros x y hx hy hxy
    have h_deriv : ∀ t : ℝ, x ≤ t → t ≤ y → |deriv (fun t => t ^ (-α)) t| ≤ α * x ^ (-α - 1) := by
      intros t hxt hyt
      have h_deriv : deriv (fun t => t ^ (-α)) t = -α * t ^ (-α - 1) := by
        norm_num [ show t ≠ 0 by linarith ];
      rw [ h_deriv, abs_mul, abs_neg, abs_of_pos hα ];
      rw [ abs_of_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith ) hα.le;
    by_cases hxy' : x = y <;> simp_all +decide [ abs_sub_comm ];
    have := exists_deriv_eq_slope ( f := fun t => t ^ ( -α ) ) ( show x < y from lt_of_le_of_ne hxy hxy' );
    obtain ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ := this ( by exact continuousOn_of_forall_continuousAt fun t ht => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ ht.1 ] ) ( by exact fun t ht => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ ht.1, ht.2 ] ) ; rw [ eq_div_iff ] at hcd <;> cases abs_cases ( x - y ) <;> cases abs_cases ( x ^ ( -α ) - y ^ ( -α ) ) <;> nlinarith [ abs_le.mp ( h_deriv c ( by linarith ) ( by linarith ) ) ] ;
  cases le_total x y <;> simp_all +decide [ abs_sub_comm ];
  · refine le_trans ( h_mean_value x y hx hy ‹_› ) ?_;
    exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith ) hα.le ) ( abs_nonneg _ );
  · rw [ abs_sub_comm ];
    refine' le_trans ( h_mean_value _ _ hy hx ‹_› ) _;
    rw [ abs_sub_comm ];
    exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith ) hα.le ) ( abs_nonneg _ )

/-
The rpow exponent cancellation: `(x ^ p) ^ (1/p) = x` for `x > 0`.
    Specialised to `p = -L/(2L-1)` and `1/p = -(2L-1)/L`.
-/
private lemma rpow_rpow_cancel_exp (x : ℝ) (hx : 0 < x) (L : ℕ) (hL : 2 ≤ L) :
    Real.rpow (Real.rpow x (-(L : ℝ) / (2 * (L : ℝ) - 1)))
              (-(2 * (L : ℝ) - 1) / (L : ℝ)) = x := by
  convert Real.rpow_mul ?_ ?_ using 1;
  rotate_left;
  exact x;
  exact le_of_lt hx;
  exact -L / ( 2 * L - 1 );
  constructor <;> intro h;
  · exact fun z => Real.rpow_mul hx.le _ _;
  · convert h ( - ( 2 * L - 1 ) / L ) using 1;
    · convert h ( - ( 2 * L - 1 ) / L ) |> Eq.symm using 1;
    · rw [ ← Real.rpow_mul ( by positivity ), div_mul_div_comm, mul_comm ];
      rw [ show ( - ( 2 * L - 1 ) * -L : ℝ ) / ( ( 2 * L - 1 ) * L ) = 1 by rw [ div_eq_iff ] <;> nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ] ; norm_num

/-! ### Corrected Theorem 5.2 -/

/-- **Theorem 5.2 (Early-time slope estimator for λ_r*, corrected form).**

    **Corrections from the original statement (Aristotle `95ddb6a0`):**
    1. The hypothesis exponent is changed from `ε^{1/L}` to `ε^{(L+1)/L}`.
       The original ε^{1/L} rate is too large relative to σ_id ≈ ε, making
       the estimator error blow up (see counterexample above). The correct
       Grönwall-derived perturbation from the μ-term is O(ε^{(L+1)/L}).
    2. Added hypothesis `hc_small : c * ((2*L-1)/L) < 1`, ensuring σ_id > 0
       (observation time before blow-up of the idealised ODE).

    The **conclusion** is unchanged: `|λ̂(ε) - λ| ≤ C · ε^{1/L} · |log ε|`.
    The exponent drops from (L+1)/L in the hypothesis to 1/L in the conclusion
    because dividing by t₀ ∝ ε^{-(2L-1)/L} absorbs one factor of ε.

    **Proof sketch (4 steps).**

    Step 1: σ_id_base := ε^{-α}·(1-cα) where α = (2L-1)/L. Then
    σ_id = σ_id_base^{-1/α} = Aε with A = (1-cα)^{-1/α} > 0, and
    σ_id^{-α} = σ_id_base = (1-cα)·ε^{-α} (by rpow exponent cancellation).
    The idealised inversion gives exactly λ.

    Step 2: By rpow_neg_mvt_bound on [Aε/2, ∞):
    |σ^{-α} - σ_id^{-α}| ≤ α · (Aε/2)^{-α-1} · |σ - σ_id|.

    Step 3: |est - λ| = (1/α)·|σ_id^{-α} - σ^{-α}|/t₀
    ≤ (Aε/2)^{-α-1}·K·ε^{(L+1)/L}·|log ε|/(c/λ·ε^{-α})
    = 2^{α+1}·A^{-α-1}·K·λ/c · ε^{1/L} · |log ε|.

    Step 4: Set C := 2^{α+1}·A^{-α-1}·K·λ/c. Each factor is positive ⇒ C > 0.
    Choose ε₀ from eps_rpow_log_eventually_small with δ = A/2 to ensure
    σ ∈ [Aε/2, 3Aε/2] for ε < ε₀.
-/
theorem lambda_hat_early_slope_rate
    (L : ℕ) (hL : 2 ≤ L)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma_at_t0 : ℝ → ℝ)
    (K_early : ℝ) (hK_early_pos : 0 < K_early)
    (h_early_slope_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        0 < sigma_at_t0 ε ∧
        |sigma_at_t0 ε
          - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / L)
                      - ((2 * (L : ℝ) - 1) / L) * lambda
                          * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L)))
                      (-(L : ℝ) / (2 * (L : ℝ) - 1))|
          ≤ K_early * ε ^ (((L : ℝ) + 1) / (L : ℝ)) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |((L : ℝ) / (2 * (L : ℝ) - 1))
              * (ε ^ (-(2 * (L : ℝ) - 1) / L)
                  - Real.rpow (sigma_at_t0 ε) (-(2 * (L : ℝ) - 1) / L))
              / (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L))
           - lambda|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  revert hK_early_pos h_early_slope_bound;
  intro hK_early_pos h_early_slope_bound
  set α : ℝ := (2 * L - 1) / L
  set β : ℝ := 1 - c * α
  have hα_pos : 0 < α := by
    exact div_pos ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity )
  have hβ_pos : 0 < β := by
    exact sub_pos_of_lt hc_small;
  obtain ⟨ε_0, hε_0_pos, hε_0_lt_one, hε_0_bound⟩ : ∃ ε_0 : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε_0 → K_early * ε ^ (1 / L : ℝ) * |Real.log ε| < (β ^ (-1 / α : ℝ)) / 2 := by
    convert eps_rpow_log_eventually_small L hL K_early ( β ^ ( -1 / α ) / 2 ) hK_early_pos ( half_pos ( Real.rpow_pos_of_pos hβ_pos _ ) ) using 1;
  refine' ⟨ ε_0, 2 ^ ( α + 1 ) * ( β ^ ( -1 / α ) ) ^ ( -α - 1 ) * K_early * lambda / c, hε_0_pos, hε_0_lt_one, _, _ ⟩;
  · positivity;
  · intro ε hε_pos hε_lt_ε_0
    have h_sigma_bound : |sigma_at_t0 ε - (β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)| ≤ K_early * ε ^ ((L + 1) / L : ℝ) * |Real.log ε| := by
      simp +zetaDelta at *;
      grind;
    have h_mean_value_bound : |(sigma_at_t0 ε) ^ (-α : ℝ) - (β * ε ^ (-α : ℝ))| ≤ α * (β ^ (-1 / α : ℝ) * ε / 2) ^ (-α - 1 : ℝ) * |sigma_at_t0 ε - (β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)| := by
      have h_mean_value_bound : |(sigma_at_t0 ε) ^ (-α : ℝ) - ((β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)) ^ (-α : ℝ)| ≤ α * (β ^ (-1 / α : ℝ) * ε / 2) ^ (-α - 1 : ℝ) * |sigma_at_t0 ε - (β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)| := by
        apply rpow_neg_mvt_bound α (sigma_at_t0 ε) ((β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)) (β ^ (-1 / α : ℝ) * ε / 2) hα_pos (h_early_slope_bound ε hε_pos (by linarith)).left (by
        exact Real.rpow_pos_of_pos ( mul_pos hβ_pos ( Real.rpow_pos_of_pos hε_pos _ ) ) _) (by
        positivity) (by
        have h_sigma_bound : |sigma_at_t0 ε - (β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)| ≤ K_early * ε ^ (1 / L : ℝ) * |Real.log ε| * ε := by
          convert h_sigma_bound using 1 ; ring;
          rw [ Real.rpow_add hε_pos, Real.rpow_mul hε_pos.le ] ; norm_num [ show L ≠ 0 by positivity ] ; ring;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ];
        have h_sigma_bound : |sigma_at_t0 ε - (β * ε ^ (-α : ℝ)) ^ (-1 / α : ℝ)| < (β ^ (-1 / α : ℝ)) * ε / 2 := by
          exact h_sigma_bound.trans_lt ( by nlinarith [ hε_0_bound ε hε_pos hε_lt_ε_0, show 0 < ε by positivity ] );
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] at * ; ring_nf at * ; norm_num at *;
        rw [ mul_inv_cancel₀ ( ne_of_gt hα_pos ) ] at * ; norm_num at * ; linarith [ abs_lt.mp h_sigma_bound ]) (by
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num [ hα_pos.ne' ];
        exact mul_le_of_le_one_right ( by positivity ) ( by norm_num ));
      convert h_mean_value_bound using 2;
      rw [ ← Real.rpow_mul ( by positivity ), neg_div, mul_comm ] ; norm_num [ hα_pos.ne' ];
    have h_estimator_error : |(L / (2 * L - 1)) * (ε ^ (-α : ℝ) - (sigma_at_t0 ε) ^ (-α : ℝ)) / (c * lambda⁻¹ * ε ^ (-α : ℝ)) - lambda| ≤ (1 / α) * α * (β ^ (-1 / α : ℝ) * ε / 2) ^ (-α - 1 : ℝ) * K_early * ε ^ ((L + 1) / L : ℝ) * |Real.log ε| / (c * lambda⁻¹ * ε ^ (-α : ℝ)) := by
      have h_estimator_error : |(L / (2 * L - 1)) * (ε ^ (-α : ℝ) - (sigma_at_t0 ε) ^ (-α : ℝ)) / (c * lambda⁻¹ * ε ^ (-α : ℝ)) - lambda| = (1 / α) * |(sigma_at_t0 ε) ^ (-α : ℝ) - β * ε ^ (-α : ℝ)| / (c * lambda⁻¹ * ε ^ (-α : ℝ)) := by
        rw [ show ( L : ℝ ) / ( 2 * L - 1 ) = 1 / α by rw [ div_eq_div_iff ] <;> nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * ( L : ℝ ) - 1 ) ( by positivity : ( L : ℝ ) ≠ 0 ) ] ];
        rw [ show ( 1 / α * ( ε ^ ( -α ) - sigma_at_t0 ε ^ ( -α ) ) / ( c * lambda⁻¹ * ε ^ ( -α ) ) - lambda ) = ( 1 / α * ( sigma_at_t0 ε ^ ( -α ) - β * ε ^ ( -α ) ) / ( c * lambda⁻¹ * ε ^ ( -α ) ) ) * -1 by
              field_simp [hα_pos, hβ_pos, hε_pos, hlambda_pos, hc_pos]
              ring ] ; norm_num [ abs_mul, abs_div, abs_neg, abs_of_pos, hα_pos, hβ_pos, hε_pos, hlambda_pos, hc_pos ];
        rw [ abs_of_nonneg ( Real.rpow_nonneg hε_pos.le _ ) ];
      rw [h_estimator_error];
      refine' div_le_div_of_nonneg_right _ ( by positivity );
      convert mul_le_mul_of_nonneg_left ( h_mean_value_bound.trans ( mul_le_mul_of_nonneg_left h_sigma_bound <| by positivity ) ) ( by positivity : 0 ≤ 1 / α ) using 1 ; ring;
    convert h_estimator_error using 1;
    · norm_num +zetaDelta at *;
      rw [ show ( 1 - 2 * L : ℝ ) / L = - ( ( 2 * L - 1 ) / L ) by ring ];
    · rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring;
      norm_num [ Real.rpow_add hε_pos, Real.rpow_sub hε_pos, Real.rpow_neg hε_pos.le, hα_pos.ne', hβ_pos.ne', hlambda_pos.ne', hc_pos.ne', hL, ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
      norm_num [ Real.rpow_add, Real.rpow_sub, hε_pos.ne', hα_pos.ne', hβ_pos.ne', hlambda_pos.ne', hc_pos.ne', hL, ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
      norm_num [ ne_of_gt ( Real.rpow_pos_of_pos hε_pos α ) ]

/-! ## §5.2′ — Joint identifiability corollary (μ̂ from λ̂/ρ̂)

    Given the plateau estimator rate (`rho_hat_plateau_rate`) and the
    early-slope estimator rate (`lambda_hat_early_slope_rate`) at the same
    O(ε^{1/L}·|log ε|) rate, the combined estimator
        μ̂(ε) := λ̂(ε) / ρ̂(ε)
    recovers μ = λ/ρ at the same rate. This is the second half of paper
    Thm 5.2 (joint identifiability): the trajectory is a sufficient
    statistic for (λ, μ), with both parameters recovered at rate
    O(ε^{1/L}·|log ε|). Pure local algebra; no ODE/Aristotle work. -/

/-- **Theorem 5.2 (joint identifiability, μ̂ corollary).**

    Suppose `ρ_hat ε → ρ` and `λ_hat ε → λ` at the standard
    O(ε^{1/L}·|log ε|) rate, with `ρ = λ/μ` and `μ, ρ, λ > 0`. Then the
    combination estimator `μ̂(ε) := λ_hat ε / ρ_hat ε` satisfies

        |μ̂ ε - μ| ≤ C · ε^{1/L} · |log ε|

    for all `ε ∈ (0, ε_0)`, with explicit positive ε_0, C.

    Proof. Write
        λ̂/ρ̂ - λ/ρ = ((λ̂ - λ)·ρ - λ·(ρ̂ - ρ)) / (ρ̂·ρ).
    Shrink ε_0 so that the plateau rate forces `ρ̂ ε ≥ ρ/2`, hence the
    denominator is bounded below by `ρ²/2`. Triangle inequality on the
    numerator plus the two rate hypotheses gives the bound, with
    constant `C := 2/ρ · C_lambda + 2λ/ρ² · C_rho`. -/
theorem mu_hat_combination_rate
    (L : ℕ) (hL : 2 ≤ L)
    (rho lambda mu : ℝ)
    (hrho_pos : 0 < rho) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (hmu_def : mu = lambda / rho)
    (rho_hat lambda_hat : ℝ → ℝ)
    (ε_rho C_rho : ℝ) (hε_rho_pos : 0 < ε_rho) (hε_rho_lt1 : ε_rho < 1)
    (hC_rho_pos : 0 < C_rho)
    (h_rho_rate : ∀ ε : ℝ, 0 < ε → ε < ε_rho →
        |rho_hat ε - rho| ≤ C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
    (ε_lambda C_lambda : ℝ) (hε_lambda_pos : 0 < ε_lambda) (hε_lambda_lt1 : ε_lambda < 1)
    (hC_lambda_pos : 0 < C_lambda)
    (h_lambda_rate : ∀ ε : ℝ, 0 < ε → ε < ε_lambda →
        |lambda_hat ε - lambda| ≤ C_lambda * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε_0 →
        |lambda_hat ε / rho_hat ε - mu| ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  -- Shrink ε_0 so that C_rho·ε^{1/L}·|log ε| < ρ/2, forcing ρ̂(ε) ≥ ρ/2.
  obtain ⟨ε_pos_rho_hat, hε_pos_rho_hat_pos, hε_pos_rho_hat_lt1, hε_pos_rho_hat_bound⟩ :=
    eps_rpow_log_eventually_small L hL C_rho (rho / 2) hC_rho_pos (by linarith)
  -- Final ε_0 is the min of ε_rho, ε_lambda, ε_pos_rho_hat.
  set ε_0 : ℝ := min (min ε_rho ε_lambda) ε_pos_rho_hat
  have hε_0_pos : 0 < ε_0 := lt_min (lt_min hε_rho_pos hε_lambda_pos) hε_pos_rho_hat_pos
  have hε_0_lt1 : ε_0 < 1 :=
    (min_le_left _ _).trans_lt
      ((min_le_left _ _).trans_lt hε_rho_lt1)
  -- Constant for the combined bound.
  set C : ℝ := 2 / rho * C_lambda + 2 * lambda / rho ^ 2 * C_rho
  have hC_pos : 0 < C := by
    have h1 : 0 < 2 / rho * C_lambda := by positivity
    have h2 : 0 < 2 * lambda / rho ^ 2 * C_rho := by positivity
    linarith
  refine ⟨ε_0, C, hε_0_pos, hε_0_lt1, hC_pos, ?_⟩
  intro ε hε_pos hε_lt_ε0
  have hε_lt_ε_rho : ε < ε_rho :=
    hε_lt_ε0.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε_lt_ε_lambda : ε < ε_lambda :=
    hε_lt_ε0.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε_lt_ε_pos : ε < ε_pos_rho_hat :=
    hε_lt_ε0.trans_le (min_le_right _ _)
  have h_rho := h_rho_rate ε hε_pos hε_lt_ε_rho
  have h_lambda := h_lambda_rate ε hε_pos hε_lt_ε_lambda
  have h_small := hε_pos_rho_hat_bound ε hε_pos hε_lt_ε_pos
  -- ρ̂(ε) is bounded below by ρ/2.
  have h_rho_hat_lower : rho / 2 ≤ rho_hat ε := by
    have h1 : |rho_hat ε - rho| < rho / 2 := lt_of_le_of_lt h_rho h_small
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  have h_rho_hat_pos : 0 < rho_hat ε := by linarith
  -- Denominator bound: ρ̂·ρ ≥ ρ²/2.
  have h_denom_lower : rho ^ 2 / 2 ≤ rho_hat ε * rho := by
    have : rho / 2 * rho ≤ rho_hat ε * rho :=
      mul_le_mul_of_nonneg_right h_rho_hat_lower hrho_pos.le
    nlinarith
  have h_denom_pos : 0 < rho_hat ε * rho := mul_pos h_rho_hat_pos hrho_pos
  -- Algebraic identity: λ̂/ρ̂ - λ/ρ = ((λ̂ - λ)·ρ - λ·(ρ̂ - ρ)) / (ρ̂·ρ).
  have h_identity : lambda_hat ε / rho_hat ε - mu =
      ((lambda_hat ε - lambda) * rho - lambda * (rho_hat ε - rho))
        / (rho_hat ε * rho) := by
    rw [hmu_def]
    field_simp
    ring
  rw [h_identity, abs_div]
  -- Bound the numerator by triangle inequality.
  have h_num_bound :
      |(lambda_hat ε - lambda) * rho - lambda * (rho_hat ε - rho)|
        ≤ rho * (C_lambda * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
          + lambda * (C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
    have h1 : |(lambda_hat ε - lambda) * rho|
                ≤ rho * (C_lambda * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
      rw [abs_mul, abs_of_pos hrho_pos, mul_comm]
      exact mul_le_mul_of_nonneg_left h_lambda hrho_pos.le
    have h2 : |lambda * (rho_hat ε - rho)|
                ≤ lambda * (C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
      rw [abs_mul, abs_of_pos hlambda_pos]
      exact mul_le_mul_of_nonneg_left h_rho hlambda_pos.le
    calc |(lambda_hat ε - lambda) * rho - lambda * (rho_hat ε - rho)|
        ≤ |(lambda_hat ε - lambda) * rho| + |lambda * (rho_hat ε - rho)| :=
          abs_sub _ _
      _ ≤ rho * (C_lambda * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
          + lambda * (C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := add_le_add h1 h2
  -- Combine numerator bound with denominator lower bound.
  have h_denom_abs : |rho_hat ε * rho| = rho_hat ε * rho :=
    abs_of_pos h_denom_pos
  rw [h_denom_abs]
  have h_eps_log_nn : 0 ≤ ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
    have := Real.rpow_nonneg hε_pos.le ((1 : ℝ) / L)
    have := abs_nonneg (Real.log ε)
    positivity
  -- Show: numerator / denominator ≤ C · ε^{1/L} · |log ε|.
  -- Equivalent to: numerator ≤ C · ε^{1/L} · |log ε| · denominator.
  rw [div_le_iff₀ h_denom_pos]
  calc |(lambda_hat ε - lambda) * rho - lambda * (rho_hat ε - rho)|
      ≤ rho * (C_lambda * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
        + lambda * (C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := h_num_bound
    _ = (rho * C_lambda + lambda * C_rho) * (ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by ring
    _ ≤ (rho * C_lambda + lambda * C_rho)
          * (ε ^ ((1 : ℝ) / L) * |Real.log ε|)
        * ((rho_hat ε * rho) / (rho ^ 2 / 2)) := by
          have h_ratio_ge_one : 1 ≤ (rho_hat ε * rho) / (rho ^ 2 / 2) := by
            rw [le_div_iff₀ (by positivity)]
            linarith
          have h_lhs_nn : 0 ≤ (rho * C_lambda + lambda * C_rho)
                              * (ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by positivity
          nlinarith [h_lhs_nn, h_ratio_ge_one]
    _ = C * ε ^ ((1 : ℝ) / L) * |Real.log ε| * (rho_hat ε * rho) := by
          show (rho * C_lambda + lambda * C_rho)
                  * (ε ^ ((1 : ℝ) / L) * |Real.log ε|)
                * ((rho_hat ε * rho) / (rho ^ 2 / 2))
              = (2 / rho * C_lambda + 2 * lambda / rho ^ 2 * C_rho)
                  * ε ^ ((1 : ℝ) / L) * |Real.log ε| * (rho_hat ε * rho)
          have hrho_ne : rho ≠ 0 := hrho_pos.ne'
          field_simp

end JepaRhoRecovery
