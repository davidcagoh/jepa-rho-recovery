/-
# JepaRhoRecovery.EarlySlopeGronwall

Helper file for `early_slope_gronwall_bound`.
Separated to avoid axiom imports from CriticalTime.lean.
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Filter

namespace JepaRhoRecovery

/-! ### Helper 1: v-transform lower bound -/

set_option maxHeartbeats 800000 in
-- reason: mirrors neg_branch_v_lower_bound
lemma pos_v_lower_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (T : ℝ) (hT : 0 < T) :
    Real.rpow (sigma 0) (-(2 * (L : ℝ) - 1) / L)
      + (2 * (L : ℝ) - 1) / L * (-lambda) * T
      ≤ Real.rpow (sigma T) (-(2 * (L : ℝ) - 1) / L) := by
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 T, deriv (fun t => (sigma t).rpow (-(2 * L - 1) / L : ℝ) - (sigma 0).rpow (-(2 * L - 1) / L : ℝ) - (2 * L - 1) / L * (-lambda) * t) c = ( (sigma T).rpow (-(2 * L - 1) / L : ℝ) - (sigma 0).rpow (-(2 * L - 1) / L : ℝ) - (2 * L - 1) / L * (-lambda) * T ) / (T - 0) := by
    have := exists_deriv_eq_slope ( f := fun t => ( sigma t |> Real.rpow ) ( - ( 2 * L - 1 ) / L ) - ( sigma 0 |> Real.rpow ) ( - ( 2 * L - 1 ) / L ) - ( 2 * L - 1 ) / L * -lambda * t ) hT;
    convert this _ _ using 3 <;> norm_num;
    · exact ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.rpow ( hSigma_cont.continuousOn ) continuousOn_const <| by intro t ht; exact Or.inl <| ne_of_gt <| hSigma_pos t ht.1 ) <| continuousOn_const ) <| ContinuousOn.mul ( continuousOn_const.mul continuousOn_const ) continuousOn_id;
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.sub ( DifferentiableAt.rpow ( hSigma_ode t ht.1 |> HasDerivAt.differentiableAt ) ( by norm_num ) ( by linarith [ hSigma_pos t ht.1.le ] ) ) ( differentiableAt_const _ ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_id ) ) );
  have h_deriv : deriv (fun t => (sigma t).rpow (-(2 * L - 1) / L : ℝ) - (sigma 0).rpow (-(2 * L - 1) / L : ℝ) - (2 * L - 1) / L * (-lambda) * t) c = (2 * L - 1) / L * mu * (sigma c).rpow (1 / L : ℝ) := by
    norm_num [ mul_assoc, mul_comm, mul_left_comm, hSigma_ode c hc.1.1 |> HasDerivAt.differentiableAt, ne_of_gt ( hSigma_pos c hc.1.1.le ) ];
    rw [ hSigma_ode c hc.1.1 |> HasDerivAt.deriv ] ; ring;
    norm_num [ show L ≠ 0 by linarith, Real.rpow_def_of_pos ( hSigma_pos c hc.1.1.le ) ] ; ring;
    norm_num [ mul_assoc, ← Real.exp_add ] ; ring;
    rw [ show ( Real.exp ( ( L : ℝ ) ⁻¹ * Real.log ( sigma c ) - Real.log ( sigma c ) * 3 ) ) = Real.exp ( ( L : ℝ ) ⁻¹ * Real.log ( sigma c ) ) / Real.exp ( Real.log ( sigma c ) * 3 ) by rw [ ← Real.exp_sub ] ] ; norm_num [ Real.exp_mul, Real.exp_log ( hSigma_pos c hc.1.1.le ) ] ; ring;
    norm_num [ ne_of_gt ( hSigma_pos c hc.1.1.le ) ];
  simp +zetaDelta at *;
  rw [ eq_div_iff ] at hc <;> nlinarith [ show 0 < ( 2 * L - 1 : ℝ ) / L * mu * sigma c ^ ( L : ℝ ) ⁻¹ by exact mul_pos ( mul_pos ( div_pos ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity ) ) hmu_pos ) ( Real.rpow_pos_of_pos ( hSigma_pos c ( by linarith ) ) _ ) ] ;

/-! ### Helper 2: v-transform upper bound (interval-restricted σ ≤ M) -/

set_option maxHeartbeats 800000 in
-- reason: mirrors neg_branch_v_upper_bound
lemma pos_v_upper_bound_interval
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (T : ℝ) (hT : 0 < T)
    (M : ℝ) (hM : 0 < M)
    (hSigma_le : ∀ t : ℝ, 0 ≤ t → t ≤ T → sigma t ≤ M) :
    Real.rpow (sigma T) (-(2 * (L : ℝ) - 1) / L)
      ≤ Real.rpow (sigma 0) (-(2 * (L : ℝ) - 1) / L)
        + (2 * (L : ℝ) - 1) / L * (-lambda + mu * Real.rpow M (1 / (L : ℝ))) * T := by
  -- By the Mean Value Theorem, there exists some $c \in (0, T)$ such that $g'(c) = (g(T) - g(0)) / T$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 T, deriv (fun t => (2 * L - 1) / L * (-lambda + mu * M ^ (1 / L : ℝ)) * t + (sigma 0) ^ (-(2 * L - 1) / L : ℝ) - (sigma t) ^ (-(2 * L - 1) / L : ℝ)) c = ( (2 * L - 1) / L * (-lambda + mu * M ^ (1 / L : ℝ)) * T + (sigma 0) ^ (-(2 * L - 1) / L : ℝ) - (sigma T) ^ (-(2 * L - 1) / L : ℝ)) / T := by
    have := exists_deriv_eq_slope ( f := fun t => ( 2 * L - 1 ) / L * ( -lambda + mu * M ^ ( 1 / L : ℝ ) ) * t + sigma 0 ^ ( - ( 2 * L - 1 ) / L : ℝ ) - sigma t ^ ( - ( 2 * L - 1 ) / L : ℝ ) ) hT;
    simp +zetaDelta at *;
    refine' this _ _;
    · exact ContinuousOn.sub ( ContinuousOn.add ( continuousOn_const.mul continuousOn_id ) continuousOn_const ) ( ContinuousOn.rpow ( hSigma_cont.continuousOn ) continuousOn_const <| by intro t ht; exact Or.inl <| ne_of_gt <| hSigma_pos t ht.1 );
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.add ( DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_id ) ) ( differentiableAt_const _ ) ) ( DifferentiableAt.rpow ( hSigma_ode t ht.1 |> HasDerivAt.differentiableAt ) ( by norm_num ) ( ne_of_gt ( hSigma_pos t ht.1.le ) ) ) );
  -- By definition of $g$, we know that its derivative is non-negative.
  have h_deriv_nonneg : deriv (fun t => (2 * L - 1) / L * (-lambda + mu * M ^ (1 / L : ℝ)) * t + (sigma 0) ^ (-(2 * L - 1) / L : ℝ) - (sigma t) ^ (-(2 * L - 1) / L : ℝ)) c ≥ 0 := by
    norm_num [ mul_comm, hSigma_ode c hc.1.1 |> HasDerivAt.differentiableAt ];
    norm_num [ hSigma_ode c hc.1.1 |> HasDerivAt.differentiableAt, hSigma_pos c hc.1.1.le, ne_of_gt ( hSigma_pos c hc.1.1.le ) ];
    rw [ hSigma_ode c hc.1.1 |> HasDerivAt.deriv ] ; ring_nf;
    norm_num [ show L ≠ 0 by positivity ];
    norm_num [ mul_assoc, ← Real.rpow_add ( hSigma_pos c hc.1.1.le ) ];
    rw [ show ( -3 + ( L : ℝ ) ⁻¹ ) = -3 + ( L : ℝ ) ⁻¹ by ring, Real.rpow_add ( hSigma_pos c hc.1.1.le ), Real.rpow_neg ( le_of_lt ( hSigma_pos c hc.1.1.le ) ) ] ; norm_num ; ring_nf;
    norm_num [ ne_of_gt ( hSigma_pos c hc.1.1.le ) ];
    nlinarith [ show 0 < mu * sigma c ^ ( ( L : ℝ ) ⁻¹ ) by exact mul_pos hmu_pos ( Real.rpow_pos_of_pos ( hSigma_pos c hc.1.1.le ) _ ), show mu * sigma c ^ ( ( L : ℝ ) ⁻¹ ) ≤ mu * M ^ ( ( L : ℝ ) ⁻¹ ) by exact mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( le_of_lt ( hSigma_pos c hc.1.1.le ) ) ( hSigma_le c hc.1.1.le hc.1.2.le ) ( by positivity ) ) hmu_pos.le, show ( L : ℝ ) ⁻¹ ≤ 1 by exact inv_le_one_of_one_le₀ ( by norm_cast; linarith ) ];
  norm_num at *; rw [ eq_div_iff ] at hc <;> nlinarith;

/-! ### Helper 3: rpow inversion bound -/

set_option maxHeartbeats 400000 in
-- reason: rpow chain rule algebra
lemma sigma_le_of_v_ge
    (x m α : ℝ) (hx_pos : 0 < x) (hm_pos : 0 < m) (hα_pos : 0 < α)
    (hv : m ≤ x ^ (-α)) :
    x ≤ m ^ (-(1 / α)) := by
  have hx_exp : x = (x ^ (-α)) ^ (-1 / α) := by
    rw [ ← Real.rpow_mul hx_pos.le, mul_div ] ; ring_nf ; norm_num [ hα_pos.ne' ];
  convert hx_exp.le.trans ( Real.rpow_le_rpow_of_nonpos ( by positivity ) hv _ ) using 1 ; ring_nf;
  exact div_nonpos_of_nonpos_of_nonneg ( by norm_num ) hα_pos.le

/-! ### Helper 4: rpow Lipschitz (MVT for x^s with s < 0) -/

set_option maxHeartbeats 400000 in
-- reason: MVT via exists_deriv_eq_slope
lemma rpow_lip_of_pos
    (x y m s : ℝ) (hx : 0 < x) (hy : 0 < y) (hm_x : m ≤ x) (hm_y : m ≤ y)
    (hm_pos : 0 < m) (hs_neg : s < 0) :
    |x ^ s - y ^ s| ≤ |s| * m ^ (s - 1) * |x - y| := by
  rcases eq_or_ne x y with rfl | hxy;
  · norm_num;
  · cases' lt_or_gt_of_ne hxy with hxy hxy;
    · obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv (fun t => t ^ s) c = (y ^ s - x ^ s) / (y - x) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ ht.1 ] ;
        · exact DifferentiableOn.rpow differentiableOn_id ( differentiableOn_const _ ) ( by intro t ht; linarith [ ht.1 ] );
      have h_deriv : |deriv (fun t => t ^ s) c| = |s| * c ^ (s - 1) := by
        rw [ Real.deriv_rpow_const ] ; norm_num [ show c ≠ 0 by linarith [ hc.1.1 ] ];
        exact Or.inl ( Real.rpow_nonneg ( by linarith [ hc.1.1 ] ) _ );
      have h_c_le_m : c ^ (s - 1) ≤ m ^ (s - 1) := by
        rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc.1.1, hc.1.2 ];
      simp_all +decide [ abs_div, abs_sub_comm, mul_assoc, mul_comm, mul_left_comm ];
      rw [ div_eq_iff ] at h_deriv <;> nlinarith [ abs_pos.mpr ( sub_ne_zero.mpr ‹¬x = y› ), abs_nonneg ( x ^ s - y ^ s ), abs_nonneg s, mul_le_mul_of_nonneg_left h_c_le_m ( abs_nonneg s ) ];
    · obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo y x, (x^s - y^s) / (x - y) = s * c^(s-1) := by
        have := exists_deriv_eq_slope ( f := fun t => t ^ s ) hxy;
        exact this ( continuousOn_of_forall_continuousAt fun t ht => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ ht.1 ] ) ( fun t ht => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ ht.1, ht.2 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, hc₂.symm ▸ by norm_num [ show c ≠ 0 by linarith [ hc₁.1 ] ] ⟩;
      have hc_le_m : c^(s-1) ≤ m^(s-1) := by
        rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc.1.1, hc.1.2 ];
      rw [ div_eq_iff ( sub_ne_zero_of_ne ‹_› ) ] at hc;
      rw [ hc.2, abs_mul, abs_mul, abs_of_nonpos hs_neg.le, abs_of_nonneg ( sub_nonneg.mpr hxy.le ) ];
      exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.rpow_nonneg ( by linarith [ hc.1.1 ] ) _ ) ] ; exact hc_le_m ) ( by linarith ) ) ( by linarith )

/-! ### Helper 5: σ bound on interval

Under pos_v_lower_bound, σ(t) ≤ A*ε for t ∈ [0, t₀].
A = (1-cα)^(-L/(2L-1)), α = (2L-1)/L.
-/

set_option maxHeartbeats 800000 in
-- reason: uses pos_v_lower_bound + sigma_le_of_v_ge + rpow algebra
lemma sigma_le_Aeps_on_interval
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hSigma_init : sigma 0 = ε)
    (t : ℝ) (ht : 0 ≤ t)
    (ht_le : t ≤ c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))) :
    sigma t ≤ (1 - c * ((2 * (L : ℝ) - 1) / (L : ℝ))) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1)) * ε := by
  -- Apply pos_v_lower_bound at t to get σ(0)^(-α) + α*(-λ)*t ≤ σ(t)^(-α).
  have h_pos_lower_bound : Real.rpow (sigma 0) (-(2 * (L : ℝ) - 1) / L) + (2 * (L : ℝ) - 1) / L * (-lambda) * t ≤ Real.rpow (sigma t) (-(2 * (L : ℝ) - 1) / L) := by
    convert pos_v_lower_bound L hL lambda mu hmu_pos sigma hSigma_pos hSigma_cont hSigma_ode t using 1;
    cases lt_or_eq_of_le ht <;> aesop;
  -- By sigma_le_of_v_ge: σ(t) ≤ ((1-cα)*ε^(-α))^(-1/α).
  have h_sigma_le : sigma t ≤ ((1 - c * ((2 * (L : ℝ) - 1) / L)) * ε ^ (-(2 * (L : ℝ) - 1) / L)) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1)) := by
    have h_sigma_le : Real.rpow (sigma t) (-(2 * (L : ℝ) - 1) / L) ≥ (1 - c * ((2 * (L : ℝ) - 1) / L)) * ε ^ (-(2 * (L : ℝ) - 1) / L) := by
      simp_all +decide [ div_eq_mul_inv ];
      nlinarith [ show 0 < ( L : ℝ ) ⁻¹ * ( 2 * L - 1 ) by exact mul_pos ( inv_pos.mpr ( by positivity ) ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ), show 0 < ( L : ℝ ) ⁻¹ * ( 2 * L - 1 ) * lambda by exact mul_pos ( mul_pos ( inv_pos.mpr ( by positivity ) ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ) hlambda_pos, mul_inv_cancel_left₀ hlambda_pos.ne' ( ε ^ ( ( 1 - 2 * L : ℝ ) * ( L : ℝ ) ⁻¹ ) ) ];
    convert sigma_le_of_v_ge _ _ _ _ _ _ _ using 1 <;> norm_num;
    rotate_left 1;
    exact ( 1 - c * ( ( 2 * L - 1 ) / L ) ) * ε ^ ( ( 1 - 2 * L ) / L : ℝ );
    exact ( 2 * L - 1 ) / L;
    · exact hSigma_pos t ht;
    · exact mul_pos ( sub_pos.mpr hc_small ) ( Real.rpow_pos_of_pos hε _ );
    · exact div_pos ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity );
    · convert h_sigma_le.le using 1 <;> ring;
      norm_num [ Real.rpow_def_of_pos ( hSigma_pos t ht ) ];
    · field_simp;
  convert h_sigma_le using 1 ; rw [ Real.mul_rpow ( by nlinarith ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
  norm_num [ sq, mul_assoc, ne_of_gt ( zero_lt_two.trans_le hL ) ];
  exact Or.inl ( by rw [ show ( - ( -1 + L * 2 : ℝ ) ⁻¹ + L * ( ( -1 + L * 2 : ℝ ) ⁻¹ * 2 ) ) = 1 by linarith [ inv_mul_cancel₀ ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] : ( -1 + L * 2 : ℝ ) ≠ 0 ) ] ] ; norm_num )

/-! ### Helper 6: Core difference bound

This combines all the helpers to bound the difference between σ(t₀) and σ_id(t₀).
The bound is expressed in terms of rpow to avoid premature simplification.
-/

set_option maxHeartbeats 1600000 in
-- reason: combines v_lower + sigma_bound + v_upper + rpow_lip
lemma core_diff_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hSigma_init : sigma 0 = ε) :
    let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    |sigma t₀
      - Real.rpow (ε ^ (-α) - α * lambda * t₀) (-(L : ℝ) / (2 * (L : ℝ) - 1))|
    ≤ ((L : ℝ) / (2 * (L : ℝ) - 1)) *
        ((1 - c * α) * ε ^ (-α)) ^ (-((L : ℝ) / (2 * (L : ℝ) - 1)) - 1) *
        (α * mu * (A * ε) ^ ((1 : ℝ) / (L : ℝ)) * t₀) := by
  -- Apply the pos_v_lower_bound lemma.
  have h_pos_v_lower_bound : let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    (ε ^ (-α) - α * lambda * t₀) ≤ (sigma t₀) ^ (-α) := by
      convert pos_v_lower_bound L hL lambda mu hmu_pos sigma hSigma_pos hSigma_cont hSigma_ode ( c * lambda⁻¹ * ε ^ ( - ( 2 * L - 1 ) / L : ℝ ) ) ( by positivity ) using 1 ; ring;
      · aesop;
      · grind +suggestions;
  have h_pos_v_upper_bound_interval : let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    (sigma t₀) ^ (-α) ≤ ε ^ (-α) - α * lambda * t₀ + α * mu * (A * ε) ^ (1 / (L : ℝ)) * t₀ := by
      convert pos_v_upper_bound_interval L hL lambda mu hmu_pos sigma hSigma_pos hSigma_cont hSigma_ode _ _ _ _ using 1;
      rotate_left;
      exact c * lambda⁻¹ * ε ^ ( - ( 2 * L - 1 ) / L : ℝ );
      exact mul_pos ( mul_pos hc_pos ( inv_pos.mpr hlambda_pos ) ) ( Real.rpow_pos_of_pos hε _ );
      exact ( 1 - c * ( ( 2 * L - 1 ) / L : ℝ ) ) ^ ( -L / ( 2 * L - 1 ) : ℝ ) * ε;
      · exact mul_pos ( Real.rpow_pos_of_pos ( sub_pos.mpr hc_small ) _ ) hε;
      · constructor <;> intro h;
        · norm_num [ neg_div, hSigma_init ];
          grind +extAll;
        · convert h _ using 1;
          · norm_num [ neg_div ];
            ring;
          · norm_num [ hSigma_init ] ; ring;
          · convert sigma_le_Aeps_on_interval L hL lambda mu hlambda_pos hmu_pos c hc_pos hc_small sigma hSigma_pos hSigma_cont hSigma_ode ε hε hε1 hSigma_init using 1;
  have h_rpow_lip_of_pos : let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    |(sigma t₀) ^ (-α) - (ε ^ (-α) - α * lambda * t₀)| ≤ α * mu * (A * ε) ^ (1 / (L : ℝ)) * t₀ := by
      exact abs_le.mpr ⟨ by linarith, by linarith ⟩;
  have h_rpow_lip_of_pos : let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    |(sigma t₀) - (ε ^ (-α) - α * lambda * t₀) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))| ≤ |(sigma t₀) ^ (-α) - (ε ^ (-α) - α * lambda * t₀)| * |-(L : ℝ) / (2 * (L : ℝ) - 1)| * ((1 - c * α) * ε ^ (-α)) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1) - 1) := by
      convert rpow_lip_of_pos ( sigma ( c * lambda⁻¹ * ε ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) ) ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) ) ( ε ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) - ( ( 2 * L - 1 ) / L : ℝ ) * lambda * ( c * lambda⁻¹ * ε ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) ) ) ( ( 1 - c * ( ( 2 * L - 1 ) / L : ℝ ) ) * ε ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) ) ( -L / ( 2 * L - 1 ) : ℝ ) _ _ _ _ _ _ using 1 <;> norm_num;
      any_goals nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast, show ( 0 : ℝ ) < ε ^ ( - ( ( 2 * L - 1 ) / L : ℝ ) ) by positivity ];
      any_goals rw [ div_lt_iff₀ ] <;> nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast ];
      · rw [ ← Real.rpow_mul ( le_of_lt ( hSigma_pos _ ( by positivity ) ) ) ] ; ring_nf ; norm_num [ show L ≠ 0 by positivity ] ;
        norm_num [ sq, mul_assoc, ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
        rw [ show ( L : ℝ ) * ( -1 + L * 2 : ℝ ) ⁻¹ * 2 - ( -1 + L * 2 : ℝ ) ⁻¹ = 1 by linarith [ mul_inv_cancel₀ ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] : ( -1 + L * 2 : ℝ ) ≠ 0 ) ] ] ; norm_num ; ring;
      · exact Real.rpow_pos_of_pos ( hSigma_pos _ ( by positivity ) ) _;
      · field_simp;
        rw [ mul_div, div_lt_iff₀ ] at hc_small <;> first | positivity | linarith;
      · convert h_pos_v_lower_bound using 1 ; ring;
        norm_num [ hlambda_pos.ne' ];
      · ring_nf; norm_num [ hlambda_pos.ne' ];
  simp_all +decide [ abs_div, abs_neg, abs_of_pos ];
  convert h_rpow_lip_of_pos.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ‹_› <| by positivity ) <| by exact Real.rpow_nonneg ( mul_nonneg ( sub_nonneg.2 hc_small.le ) <| Real.rpow_nonneg hε.le _ ) _ ) using 1 ; ring;
  rw [ abs_of_nonneg ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ] ; ring

/-! ### Helper 7: Exponent simplification

The product from core_diff_bound simplifies to const * ε^((L+1)/L).
-/

set_option maxHeartbeats 800000 in
-- reason: rpow algebra
lemma exponent_simplification
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (ε : ℝ) (hε : 0 < ε) :
    let α := (2 * (L : ℝ) - 1) / (L : ℝ)
    let t₀ := c * lambda⁻¹ * ε ^ (-α)
    let A := (1 - c * α) ^ (-(L : ℝ) / (2 * (L : ℝ) - 1))
    ((L : ℝ) / (2 * (L : ℝ) - 1)) *
      ((1 - c * α) * ε ^ (-α)) ^ (-((L : ℝ) / (2 * (L : ℝ) - 1)) - 1) *
      (α * mu * (A * ε) ^ ((1 : ℝ) / (L : ℝ)) * t₀)
    = ((L : ℝ) / (2 * (L : ℝ) - 1)) *
      (1 - c * α) ^ (-((L : ℝ) / (2 * (L : ℝ) - 1)) - 1) *
      α * mu * A ^ ((1 : ℝ) / (L : ℝ)) * c * lambda⁻¹ *
      ε ^ (((L : ℝ) + 1) / (L : ℝ)) := by
  simp +zetaDelta at *;
  rw [ Real.mul_rpow ( sub_nonneg.2 hc_small.le ) ( by positivity ), Real.mul_rpow ( by exact Real.rpow_nonneg ( sub_nonneg.2 hc_small.le ) _ ) ( by positivity ) ] ; ring;
  norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hL ) ];
  norm_num [ ← mul_assoc, ← Real.rpow_add hε, ← Real.rpow_mul hε.le ] ; ring;
  norm_num [ show L ≠ 0 by linarith, show ( -1 + L * 2 : ℝ ) ≠ 0 by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ] ; ring;
  rw [ show ( 1 + ( L : ℝ ) ⁻¹ ) = ( L : ℝ ) ⁻¹ + ( L * ( -1 + L * 2 : ℝ ) ⁻¹ * 2 - ( -1 + L * 2 : ℝ ) ⁻¹ ) by nlinarith [ mul_inv_cancel₀ ( by positivity : ( L : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] : ( -1 + L * 2 : ℝ ) ≠ 0 ) ] ] ; ring;
  rw [ show ( L : ℝ ) * ( -1 + L * 2 : ℝ ) ⁻¹ * 2 + ( ( L : ℝ ) ⁻¹ - ( -1 + L * 2 : ℝ ) ⁻¹ ) = ( L : ℝ ) * ( -1 + L * 2 : ℝ ) ⁻¹ * 2 - ( -1 + L * 2 : ℝ ) ⁻¹ + ( L : ℝ ) ⁻¹ by ring ] ; rw [ Real.rpow_add hε ] ; ring;

/-! ### Main theorem -/

set_option maxHeartbeats 1600000 in
-- reason: assembly of all helpers
theorem early_slope_gronwall_bound_aux
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      |sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ)))
        - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))
                    - ((2 * (L : ℝ) - 1) / (L : ℝ)) * lambda
                        * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))))
                    (-(L : ℝ) / (2 * (L : ℝ) - 1))|
        ≤ C * ε ^ (((L : ℝ) + 1) / (L : ℝ)) := by
  refine' ⟨ ( L / ( 2 * L - 1 ) ) * ( 1 - c * ( ( 2 * L - 1 ) / L ) ) ^ ( - ( L / ( 2 * L - 1 ) ) - 1 : ℝ ) * ( ( 2 * L - 1 ) / L ) * mu * ( ( 1 - c * ( ( 2 * L - 1 ) / L ) ) ^ ( - ( L : ℝ ) / ( 2 * L - 1 ) ) ) ^ ( 1 / L : ℝ ) * c * lambda⁻¹ + 1, _, _ ⟩;
  · refine' add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg _ _ ) _ ) _ ) _ ) _ ) _ ) zero_lt_one;
    any_goals positivity;
    · exact div_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] );
    · exact Real.rpow_nonneg ( sub_nonneg.2 hc_small.le ) _;
    · exact div_nonneg ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity );
    · exact Real.rpow_nonneg ( Real.rpow_nonneg ( sub_nonneg.2 hc_small.le ) _ ) _;
  · intro ε hε hε';
    have := @core_diff_bound L hL lambda mu hlambda_pos hmu_pos c hc_pos hc_lt_one hc_small ( sigma ε ) ( fun t ht => hSigma_pos ε hε hε' t ht ) ( hSigma_cont ε hε hε' ) ( fun t ht => hSigma_ode ε hε hε' t ht ) ε hε hε' ( hSigma_init ε hε hε' );
    have := @exponent_simplification L hL lambda mu hlambda_pos hmu_pos c hc_pos hc_small ε hε;
    simp_all +decide [ neg_div ];
    rw [ show ( 1 - 2 * L : ℝ ) / L = - ( ( 2 * L - 1 ) / L ) by ring ] ; linarith [ show 0 < ε ^ ( ( L + 1 : ℝ ) / L ) by positivity ] ;

end JepaRhoRecovery