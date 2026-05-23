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
  -- Aristotle job d7a13dd1 (session 90).
  -- Factorization $a^L - b^L = (a-b) Σ a^k b^{L-1-k}$ with $a = σ(ε)$, $b = ρ^{1/L}$.
  have h_factorization : ∀ ε, 0 < ε → ε < 1 → |sigma_at_T ε ^ L - rho| ≤ |sigma_at_T ε - rho.rpow (1 / L)| * ∑ k ∈ Finset.range L, |sigma_at_T ε| ^ k * |rho.rpow (1 / L)| ^ (L - 1 - k) := by
    intros ε hε_pos hε_lt_1
    have h_factor : sigma_at_T ε ^ L - rho = (sigma_at_T ε - rho.rpow (1 / L)) * (∑ k ∈ Finset.range L, sigma_at_T ε ^ k * (rho.rpow (1 / L)) ^ (L - 1 - k)) := by
      convert geom_sum₂_mul ( sigma_at_T ε ) ( rho ^ ( 1 / ( L : ℝ ) ) ) L using 1 ; norm_num [ hrho_pos.le ];
      · rw [ geom_sum₂_mul ];
        rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ];
      · simp +zetaDelta at *;
        rw [ ← geom_sum₂_mul, mul_comm ];
    rw [ h_factor, abs_mul ];
    exact mul_le_mul_of_nonneg_left ( le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun _ _ => by rw [ abs_mul, abs_pow, abs_pow ] ) ) ( abs_nonneg _ );
  obtain ⟨ε_0, hε0_pos, hε0_lt_1, hε0_small⟩ : ∃ ε_0 : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ ∀ ε, 0 < ε → ε < ε_0 → |sigma_at_T ε - rho.rpow (1 / L)| ≤ rho.rpow (1 / L) / 2 := by
    have h_eps_small : Filter.Tendsto (fun ε : ℝ => K_plateau * ε ^ (1 / L : ℝ) * |Real.log ε|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h_eps_small : Filter.Tendsto (fun ε : ℝ => ε ^ (1 / L : ℝ) * |Real.log ε|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (y / L) * |y|) Filter.atBot (nhds 0) by
          have := h_log.comp Real.tendsto_log_nhdsGT_zero;
          refine' this.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring );
        suffices h_neg : Filter.Tendsto (fun z : ℝ => Real.exp (-z / L) * z) Filter.atTop (nhds 0) by
          convert h_neg.comp Filter.tendsto_neg_atBot_atTop |> Filter.Tendsto.congr' _ using 2;
          filter_upwards [ Filter.eventually_lt_atBot 0 ] with x hx using by rw [ Function.comp_apply, abs_of_neg hx ] ; ring;
        suffices h_w : Filter.Tendsto (fun w : ℝ => Real.exp (-w) * L * w) Filter.atTop (nhds 0) by
          convert h_w.comp ( Filter.tendsto_id.atTop_mul_const ( inv_pos.mpr ( by positivity : 0 < ( L : ℝ ) ) ) ) using 2 ; norm_num ; ring;
          norm_num [ show L ≠ 0 by positivity ];
        simpa [ mul_assoc, mul_comm, mul_left_comm ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |> Filter.Tendsto.const_mul ( L : ℝ ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
      simpa [ mul_assoc ] using h_eps_small.const_mul K_plateau;
    have := h_eps_small.eventually ( gt_mem_nhds <| show 0 < rho.rpow ( 1 / ( L : ℝ ) ) / 2 by exact div_pos ( Real.rpow_pos_of_pos hrho_pos _ ) zero_lt_two );
    rcases ( Metric.mem_nhdsWithin_iff.mp <| this ) with ⟨ ε, ε_pos, hε ⟩;
    exact ⟨ Min.min ε 1 / 2, by positivity, by linarith [ min_le_left ε 1, min_le_right ε 1 ], fun x hx₁ hx₂ => le_trans ( h_plateau_bound x hx₁ ( by linarith [ min_le_left ε 1, min_le_right ε 1 ] ) ) ( le_of_lt ( hε ⟨ mem_ball_zero_iff.mpr ( abs_lt.mpr ⟨ by linarith [ min_le_left ε 1, min_le_right ε 1 ], by linarith [ min_le_left ε 1, min_le_right ε 1 ] ⟩ ), hx₁ ⟩ ) ) ⟩;
  have h_bound : ∀ ε, 0 < ε → ε < ε_0 → ∑ k ∈ Finset.range L, |sigma_at_T ε| ^ k * |rho.rpow (1 / L)| ^ (L - 1 - k) ≤ L * ((3 / 2) * rho.rpow (1 / L)) ^ (L - 1) := by
    intros ε hε_pos hε_lt_ε0
    have h_sigma_bound : |sigma_at_T ε| ≤ (3 / 2) * rho.rpow (1 / L) := by
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hε0_small ε hε_pos hε_lt_ε0 ), show 0 ≤ rho.rpow ( 1 / ( L : ℝ ) ) by exact Real.rpow_nonneg hrho_pos.le _ ], by linarith [ abs_le.mp ( hε0_small ε hε_pos hε_lt_ε0 ), show 0 ≤ rho.rpow ( 1 / ( L : ℝ ) ) by exact Real.rpow_nonneg hrho_pos.le _ ] ⟩;
    refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul ( pow_le_pow_left₀ ( abs_nonneg _ ) h_sigma_bound _ ) ( pow_le_pow_left₀ ( abs_nonneg _ ) ( show |rho.rpow ( 1 / L : ℝ )| ≤ 3 / 2 * rho.rpow ( 1 / L : ℝ ) from _ ) _ ) ( by positivity ) ( by exact pow_nonneg ( by linarith [ show 0 ≤ rho.rpow ( 1 / L : ℝ ) from Real.rpow_nonneg hrho_pos.le _ ] ) _ ) ) _;
    · grind +splitIndPred;
    · simp +decide [ ← pow_add, add_comm, ← Finset.sum_range_reflect ];
  refine' ⟨ ε_0, K_plateau * L * ( 3 / 2 * rho.rpow ( 1 / L ) ) ^ ( L - 1 ), hε0_pos, hε0_lt_1, _, _ ⟩;
  · exact mul_pos ( mul_pos hK_plateau_pos ( Nat.cast_pos.mpr ( by linarith ) ) ) ( pow_pos ( mul_pos ( by norm_num ) ( Real.rpow_pos_of_pos hrho_pos _ ) ) _ );
  · intro ε hε_pos hε_lt_ε0
    specialize h_factorization ε hε_pos (by linarith)
    specialize h_plateau_bound ε hε_pos (by linarith)
    specialize h_bound ε hε_pos hε_lt_ε0;
    refine' le_trans h_factorization ( le_trans ( mul_le_mul_of_nonneg_right h_plateau_bound ( Finset.sum_nonneg fun _ _ => by positivity ) ) _ );
    convert mul_le_mul_of_nonneg_left h_bound ( show 0 ≤ K_plateau * ε ^ ( 1 / ( L : ℝ ) ) * |Real.log ε| by positivity ) using 1 ; ring

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
  -- Aristotle job d6a21f55 (session 90).
  -- Monotonicity from non-negative derivative.
  have h_mono : MonotoneOn sigma (Set.Ici 0) := by
    have h_deriv_nonneg : ∀ t > 0, 0 ≤ deriv sigma t := by
      intro t ht; rw [ hSigma_ode t ht |> HasDerivAt.deriv ] ; refine mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hmu_pos.le ) ?_ ) ?_;
      · exact Real.rpow_nonneg ( le_of_lt ( hSigma_pos t ht.le ) ) _;
      · simp +zetaDelta at *;
        exact le_trans ( pow_le_pow_left₀ ( le_of_lt ( hSigma_pos t ht.le ) ) ( le_of_lt ( hSigma_below t ht.le ) ) _ ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] );
    apply_rules [ monotoneOn_of_deriv_nonneg ];
    · exact convex_Ici _;
    · exact hSigma_cont.continuousOn;
    · exact fun t ht => ( hSigma_ode t <| by aesop ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt;
    · aesop;
  -- Monotone bounded above → converges to its supremum ≤ (λ/μ)^(1/L).
  obtain ⟨sigma_inf, h_sigma_inf⟩ : ∃ sigma_inf, Filter.Tendsto sigma atTop (nhds sigma_inf) ∧ sigma_inf ≤ (lambda / mu).rpow (1 / L) := by
    have h_bdd : BddAbove (Set.image sigma (Set.Ici 0)) := by
      exact ⟨ _, Set.forall_mem_image.2 fun t ht => le_of_lt ( hSigma_below t ht ) ⟩;
    have h_conv : Filter.Tendsto sigma atTop (nhds (sSup (Set.image sigma (Set.Ici 0)))) := by
      apply_rules [ tendsto_order.2 ⟨ _, _ ⟩ ];
      · exact fun x hx => by rcases exists_lt_of_lt_csSup ( Set.Nonempty.image _ <| Set.nonempty_Ici ) hx with ⟨ y, ⟨ t, ht, rfl ⟩, hy ⟩ ; filter_upwards [ Filter.eventually_ge_atTop t ] with u hu using hy.trans_le <| h_mono ( show 0 ≤ t by linarith [ Set.mem_Ici.mp ht ] ) ( show 0 ≤ u by linarith [ Set.mem_Ici.mp ht ] ) hu;
      · exact fun x hx => Filter.eventually_atTop.mpr ⟨ 0, fun t ht => lt_of_le_of_lt ( le_csSup h_bdd <| Set.mem_image_of_mem _ ht ) hx ⟩;
    exact ⟨ _, h_conv, le_of_tendsto_of_tendsto h_conv tendsto_const_nhds <| Filter.eventually_atTop.mpr ⟨ 0, fun t ht => le_of_lt <| hSigma_below t ht ⟩ ⟩;
  -- Suppose for contradiction $\sigma_\infty < (\lambda/\mu)^{1/L}$.
  by_contra h_contra;
  have h_deriv_pos : ∃ ε > 0, ∀ᶠ t in atTop, (HasDerivAt sigma (L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) t) ∧ (L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) > ε := by
    have h_deriv_pos : ∃ ε > 0, ∀ᶠ t in atTop, (L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) > ε := by
      have h_deriv_pos : Filter.Tendsto (fun t => L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) atTop (nhds (L * mu * (sigma_inf).rpow (2 - 1 / L) * (lambda / mu - sigma_inf ^ L))) := by
        exact Filter.Tendsto.mul ( Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.rpow h_sigma_inf.1 tendsto_const_nhds <| Or.inl <| by linarith [ show 0 < sigma_inf from lt_of_lt_of_le ( hSigma_pos 0 le_rfl ) <| le_of_tendsto_of_tendsto tendsto_const_nhds h_sigma_inf.1 <| Filter.eventually_atTop.2 ⟨ 0, fun t ht => h_mono ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht ⟩ ] ) ) ( tendsto_const_nhds.sub <| h_sigma_inf.1.pow L );
      have h_deriv_pos : L * mu * (sigma_inf).rpow (2 - 1 / L) * (lambda / mu - sigma_inf ^ L) > 0 := by
        refine' mul_pos ( mul_pos ( mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) hmu_pos ) _ ) _;
        · exact Real.rpow_pos_of_pos ( lt_of_lt_of_le ( hSigma_pos 0 le_rfl ) ( le_of_tendsto_of_tendsto tendsto_const_nhds h_sigma_inf.1 ( Filter.eventually_atTop.mpr ⟨ 0, fun t ht => h_mono ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht ⟩ ) ) ) _;
        · have h_sigma_inf_lt : sigma_inf < (lambda / mu).rpow (1 / L) := by
            exact lt_of_le_of_ne h_sigma_inf.2 fun h => h_contra <| h ▸ h_sigma_inf.1;
          have h_sigma_inf_lt_pow : sigma_inf ^ L < (lambda / mu) := by
            exact lt_of_lt_of_le ( pow_lt_pow_left₀ h_sigma_inf_lt ( le_of_tendsto_of_tendsto tendsto_const_nhds h_sigma_inf.1 <| Filter.eventually_atTop.mpr ⟨ 0, fun t ht => le_of_lt <| hSigma_pos t ht ⟩ ) <| by positivity ) <| by erw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), one_div_mul_cancel <| by positivity, Real.rpow_one ] ;
          linarith;
      exact ⟨ _, half_pos h_deriv_pos, by filter_upwards [ ‹Tendsto _ _ _›.eventually ( lt_mem_nhds <| half_lt_self h_deriv_pos ) ] with t ht using ht ⟩;
    exact ⟨ h_deriv_pos.choose, h_deriv_pos.choose_spec.1, by filter_upwards [ h_deriv_pos.choose_spec.2, Filter.eventually_gt_atTop 0 ] with t ht₁ ht₂ using ⟨ hSigma_ode t ht₂, ht₁ ⟩ ⟩;
  obtain ⟨ε, hε_pos, hε⟩ := h_deriv_pos;
  have h_mean_value : ∀ᶠ t in atTop, sigma (t + 1) - sigma t ≥ ε := by
    obtain ⟨T, hT⟩ : ∃ T, ∀ t ≥ T, HasDerivAt sigma (L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) t ∧ (L * mu * (sigma t).rpow (2 - 1 / L) * (lambda / mu - (sigma t) ^ L)) > ε := by
      exact Filter.eventually_atTop.mp hε;
    filter_upwards [ Filter.eventually_ge_atTop T ] with t ht;
    have := exists_deriv_eq_slope sigma ( show t < t + 1 by linarith );
    exact this ( hSigma_cont.continuousOn ) ( fun x hx => ( hT x ( by linarith [ hx.1 ] ) |>.1.differentiableAt.differentiableWithinAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by have := hT c ( by linarith [ hc₁.1 ] ) ; norm_num at * ; nlinarith [ this.2, this.1.deriv ] ;
  have h_mean_value : Filter.Tendsto (fun t => sigma (t + 1) - sigma t) atTop (nhds 0) := by
    simpa using Filter.Tendsto.sub ( h_sigma_inf.1.comp ( Filter.tendsto_id.atTop_add tendsto_const_nhds ) ) h_sigma_inf.1;
  exact absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds h_mean_value ‹_› ) ( by linarith )

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
  -- Aristotle job cdf0ac25 (session 90).
  -- Step 1: For each ε, obtain qualitative convergence via the corrected lemma
  have h_conv : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Filter.Tendsto (sigma ε) Filter.atTop
        (nhds (Real.rpow (lambda / mu) ((1 : ℝ) / L))) := by
    intro ε hε hε1
    exact sigma_positive_branch_converges_corrected L hL lambda mu hlambda_pos hmu_pos
      (sigma ε) (hSigma_pos ε hε hε1) (hSigma_below ε hε hε1)
      (hSigma_cont ε hε hε1) (hSigma_ode ε hε hε1)
  -- Step 2: For each ε, extract a witness time via Metric.tendsto_atTop
  have h_each : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ T : ℝ, 0 < T ∧
        |sigma ε T - Real.rpow (lambda / mu) ((1 : ℝ) / L)| ≤
          ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
    intro ε hε hε1
    have hlog_neg : Real.log ε < 0 := Real.log_neg hε hε1
    have habs_log_pos : 0 < |Real.log ε| := abs_pos.mpr (ne_of_lt hlog_neg)
    have hpow_pos : 0 < ε ^ ((1 : ℝ) / L) := by positivity
    have hδ_pos : 0 < ε ^ ((1 : ℝ) / L) * |Real.log ε| := mul_pos hpow_pos habs_log_pos
    have hconv_ε := h_conv ε hε hε1
    rw [Metric.tendsto_atTop] at hconv_ε
    obtain ⟨N, hN⟩ := hconv_ε (ε ^ ((1 : ℝ) / L) * |Real.log ε|) hδ_pos
    refine ⟨max N 1, by positivity, ?_⟩
    have hge : max N 1 ≥ N := le_max_left N 1
    have hdist := hN (max N 1) hge
    rw [Real.dist_eq] at hdist
    linarith
  -- Step 3: Bundle via Classical.choice into T : ℝ → ℝ, K_plateau = 1
  refine ⟨fun ε => if h : 0 < ε ∧ ε < 1 then (h_each ε h.1 h.2).choose else 1,
          1, one_pos, ?_, ?_⟩
  · intro ε hε hε1
    have hcond : 0 < ε ∧ ε < 1 := ⟨hε, hε1⟩
    simp only [dif_pos hcond]
    exact (h_each ε hε hε1).choose_spec.1
  · intro ε hε hε1
    have hcond : 0 < ε ∧ ε < 1 := ⟨hε, hε1⟩
    simp only [dif_pos hcond]
    have hb := (h_each ε hε hε1).choose_spec.2
    linarith [hb]

end JepaRhoRecovery
