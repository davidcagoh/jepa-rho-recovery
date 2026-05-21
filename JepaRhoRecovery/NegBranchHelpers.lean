/-
# JepaRhoRecovery.NegBranchHelpers

Helper lemmas for the negative-branch λ-rate theorem (paper Thm 7.3 part 1).
Separated into its own file to avoid axiom-declaration issues from
CriticalTime.lean in the subagent.
-/

import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Filter

namespace JepaRhoRecovery

/-
Antitone of sigma on [0, t] for the negative branch ODE.
    Adapts `sigma_negative_branch_le_init` to the (lambda, mu) parametrisation.
    Since σ' = λσ^{3-1/L} - μσ³ < 0 (λ < 0, μ > 0, σ > 0), σ is decreasing.
-/
lemma neg_branch_sigma_le_init
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (t : ℝ) (ht : 0 ≤ t) :
    sigma t ≤ sigma 0 := by
  by_contra h_contra;
  -- Apply the mean value theorem to the interval $[0, t]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 t, deriv sigma c = (sigma t - sigma 0) / (t - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact ht.lt_of_ne ( by rintro rfl; linarith );
    · exact hSigma_cont.continuousOn;
    · exact fun x hx => ( hSigma_ode x hx.1 |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt );
  rw [ hSigma_ode c hc.1.1 |> HasDerivAt.deriv ] at hc;
  rw [ eq_div_iff ] at hc <;> try linarith [ hc.1.1, hc.1.2 ];
  norm_num at *;
  exact absurd hc.2 ( by nlinarith [ show lambda * sigma c ^ ( 3 - ( L : ℝ ) ⁻¹ ) - mu * sigma c ^ 3 < 0 by exact sub_neg_of_lt ( by exact lt_of_le_of_lt ( mul_nonpos_of_nonpos_of_nonneg hlambda_neg.le ( Real.rpow_nonneg ( le_of_lt ( hSigma_pos c ( by linarith ) ) ) _ ) ) ( mul_pos hmu_pos ( pow_pos ( hSigma_pos c ( by linarith ) ) 3 ) ) ), hSigma_pos c ( by linarith ) ] )

/-
Upper bound on v(T) = σ(T)^{-(2L-1)/L}.
    From the ODE, v' = (2L-1)/L · (-λ + μ·σ^{1/L}) ≤ (2L-1)/L · (-λ + μ·σ(0)^{1/L}),
    giving v(T) ≤ v(0) + upper_rate · T.
-/
lemma neg_branch_v_upper_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - mu * (sigma t) ^ 3) t)
    (hSigma_le : ∀ t : ℝ, 0 ≤ t → sigma t ≤ sigma 0)
    (T : ℝ) (hT : 0 < T) :
    Real.rpow (sigma T) (-(2 * (L : ℝ) - 1) / L)
      ≤ Real.rpow (sigma 0) (-(2 * (L : ℝ) - 1) / L)
        + (2 * (L : ℝ) - 1) / L * (-lambda + mu * Real.rpow (sigma 0) (1 / (L : ℝ))) * T := by
  -- Define the function g(t) and show its derivative is non-negative.
  set g : ℝ → ℝ := fun t => (2 * L - 1) / L * (-lambda + mu * (sigma 0).rpow (1 / (L : ℝ))) * t + (sigma 0).rpow (-(2 * L - 1) / (L : ℝ)) - (sigma t).rpow (-(2 * L - 1) / (L : ℝ))
  have hg_deriv_nonneg : ∀ t ∈ Set.Ioo 0 T, deriv g t ≥ 0 := by
    intro t ht
    have hg_deriv : deriv g t = (2 * L - 1) / L * (-lambda + mu * (sigma 0).rpow (1 / (L : ℝ))) - (-(2 * L - 1) / L) * (sigma t) ^ (-(2 * L - 1) / (L : ℝ) - 1) * (lambda * (sigma t).rpow (3 - 1 / (L : ℝ)) - mu * (sigma t) ^ 3) := by
      convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.add ( HasDerivAt.const_mul _ ( hasDerivAt_id t ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.rpow_const ( hSigma_ode t ht.1 ) _ ) ) using 1 <;> norm_num ; ring;
      exact Or.inl <| ne_of_gt <| hSigma_pos t ht.1.le;
    -- Simplify the expression for the derivative of g.
    have hg_deriv_simplified : deriv g t = (2 * L - 1) / L * mu * ((sigma 0).rpow (1 / (L : ℝ)) - (sigma t).rpow (1 / (L : ℝ))) := by
      convert hg_deriv using 1 ; ring! ; norm_num [ ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
      norm_num [ mul_assoc, mul_left_comm, ← Real.rpow_add ( hSigma_pos t ht.1.le ) ] ; ring;
      rw [ show ( -3 + ( L : ℝ ) ⁻¹ ) = ( L : ℝ ) ⁻¹ - 3 by ring, Real.rpow_sub ( hSigma_pos t ht.1.le ) ] ; norm_num ; ring;
      norm_num [ ne_of_gt ( hSigma_pos t ht.1.le ) ];
    exact hg_deriv_simplified.symm ▸ mul_nonneg ( mul_nonneg ( div_nonneg ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity ) ) hmu_pos.le ) ( sub_nonneg.mpr ( Real.rpow_le_rpow ( le_of_lt ( hSigma_pos _ ht.1.le ) ) ( hSigma_le _ ht.1.le ) ( by positivity ) ) );
  -- Apply the mean value theorem to g on the interval [0, T].
  obtain ⟨ct, hct⟩ : ∃ ct ∈ Set.Ioo 0 T, deriv g ct = (g T - g 0) / (T - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact ContinuousOn.sub ( ContinuousOn.add ( continuousOn_const.mul continuousOn_id ) continuousOn_const ) ( ContinuousOn.rpow ( hSigma_cont.continuousOn ) continuousOn_const <| by intro t ht; exact Or.inl <| ne_of_gt <| hSigma_pos t ht.1 );
    · refine' DifferentiableOn.sub _ _;
      · exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) differentiableOn_id ) ( differentiableOn_const _ );
      · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.rpow ( hSigma_ode t ht.1 |> HasDerivAt.differentiableAt ) ( by norm_num ) ( ne_of_gt ( hSigma_pos t ht.1.le ) ) );
  simp +zetaDelta at *;
  have := hg_deriv_nonneg ct hct.1.1 hct.1.2; rw [ hct.2, le_div_iff₀ ] at this <;> linarith;

/-
Lower bound on v(T): v grows at rate ≥ (2L-1)/L · (-λ).
    From the ODE, v' = (2L-1)/L · (-λ + μ·σ^{1/L}) ≥ (2L-1)/L · (-λ),
    giving v(T) ≥ v(0) + lower_rate · T.
-/
lemma neg_branch_v_lower_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
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
  -- By the properties of the derivative, we know that if the derivative of a function is non-negative on an interval, then the function is non-decreasing on that interval.
  have h_deriv_nonneg : ∀ t ∈ Set.Ioo 0 T, 0 ≤ deriv (fun t => (sigma t).rpow (-(2 * (L : ℝ) - 1) / L) - (sigma 0).rpow (-(2 * (L : ℝ) - 1) / L) - (2 * (L : ℝ) - 1) / L * (-lambda) * t) t := by
    intro t ht; norm_num [ mul_comm, hSigma_ode t ht.1 |> HasDerivAt.differentiableAt ] ; ring_nf; norm_num;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hL ), hSigma_ode t ht.1 |> HasDerivAt.differentiableAt, ne_of_gt ( hSigma_pos t ht.1.le ) ] ; ring_nf ; norm_num [ hlambda_neg, hmu_pos, hT ] ;
    rw [ hSigma_ode t ht.1 |> HasDerivAt.deriv ] ; ring_nf ; norm_num [ ne_of_gt ( zero_lt_two.trans_le hL ), hlambda_neg, hmu_pos, hSigma_pos t ht.1.le ] ;
    norm_num [ mul_assoc, ← Real.rpow_add ( hSigma_pos t ht.1.le ) ] ; ring_nf ; (
    nlinarith [ show 0 < mu * sigma t ^ 3 * sigma t ^ ( -3 + ( L : ℝ ) ⁻¹ ) by exact mul_pos ( mul_pos hmu_pos ( pow_pos ( hSigma_pos t ht.1.le ) 3 ) ) ( Real.rpow_pos_of_pos ( hSigma_pos t ht.1.le ) _ ), inv_le_one_of_one_le₀ ( by norm_cast; linarith : ( 1 : ℝ ) ≤ L ) ]);
  -- By the Mean Value Theorem, since the derivative of $h$ is non-negative on $(0, T)$, we have $h(T) \geq h(0)$.
  have h_mvt : ∃ c ∈ Set.Ioo 0 T, deriv (fun t => (sigma t).rpow (-(2 * (L : ℝ) - 1) / L) - (sigma 0).rpow (-(2 * (L : ℝ) - 1) / L) - (2 * (L : ℝ) - 1) / L * (-lambda) * t) c = ( (sigma T).rpow (-(2 * (L : ℝ) - 1) / L) - (sigma 0).rpow (-(2 * (L : ℝ) - 1) / L) - (2 * (L : ℝ) - 1) / L * (-lambda) * T ) / T := by
    have := exists_deriv_eq_slope ( f := fun t => ( sigma t |> Real.rpow ) ( - ( 2 * L - 1 ) / L ) - ( sigma 0 |> Real.rpow ) ( - ( 2 * L - 1 ) / L ) - ( 2 * L - 1 ) / L * -lambda * t ) hT;
    simp +zetaDelta at *;
    refine' this _ _;
    · exact ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.rpow ( hSigma_cont.continuousOn ) continuousOn_const <| by intro t ht; exact Or.inl <| ne_of_gt <| hSigma_pos t ht.1 ) <| continuousOn_const ) <| ContinuousOn.mul continuousOn_const continuousOn_id;
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.sub ( DifferentiableAt.rpow ( hSigma_ode t ht.1 |> HasDerivAt.differentiableAt ) ( by norm_num ) ( ne_of_gt ( hSigma_pos t ht.1.le ) ) ) ( differentiableAt_const _ ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_id ) ) );
  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt; have := h_deriv_nonneg c hc₁; rw [ hc₂, le_div_iff₀ ] at this <;> linarith;

/-
Main theorem: negative-branch λ-rate (Thm 7.3 part 1, corrected).
-/
set_option maxHeartbeats 800000 in
theorem signed_recovery_neg_lambda_rate_core
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ T : ℝ → ℝ, ∃ K_neg : ℝ, ∃ eps_0 : ℝ,
      0 < eps_0 ∧ eps_0 < 1 ∧ 0 < K_neg ∧
      (∀ ε : ℝ, 0 < ε → ε < eps_0 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < eps_0 →
        |((L : ℝ) / (2 * (L : ℝ) - 1))
            * Real.rpow (sigma ε (T ε)) (-(2 * (L : ℝ) - 1) / L) / T ε
          - (-lambda)|
          ≤ K_neg * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
  -- Choose constants T(ε), K_neg, eps_0.
  use fun ε => ε^(-2 : ℝ) / (-lambda), (L / (2 * L - 1)) * (-lambda) + mu + 1, 1 / 3;
  refine' ⟨ by norm_num, by norm_num, _, _, _ ⟩;
  · exact add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ) ( neg_nonneg.mpr hlambda_neg.le ) ) hmu_pos.le ) zero_lt_one;
  · exact fun ε hε₁ hε₂ => div_pos ( Real.rpow_pos_of_pos hε₁ _ ) ( neg_pos.mpr hlambda_neg );
  · intro ε hε_pos hε_lt
    have h_lower_bound : (L / (2 * L - 1)) * (sigma ε (ε^(-2 : ℝ) / (-lambda))).rpow (-(2 * L - 1) / L) / (ε^(-2 : ℝ) / (-lambda)) ≥ -lambda := by
      have := neg_branch_v_lower_bound L hL lambda mu hlambda_neg hmu_pos ( sigma ε ) ( fun t ht => hSigma_pos ε hε_pos ( by linarith ) t ht ) ( hSigma_cont ε hε_pos ( by linarith ) ) ( hSigma_ode ε hε_pos ( by linarith ) ) ( ε ^ ( -2 : ℝ ) / -lambda ) ( by exact div_pos ( Real.rpow_pos_of_pos hε_pos _ ) ( neg_pos.mpr hlambda_neg ) );
      simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      simp_all +decide [ ne_of_lt, mul_assoc, mul_comm, mul_left_comm ];
      rw [ hSigma_init ε hε_pos ( by linarith ) ] at this;
      field_simp at *;
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast, show ( L : ℝ ) * ε ^ 2 * ε ^ ( ( 1 - L * 2 : ℝ ) / L ) > 0 by positivity ];
    -- From neg_branch_v_upper_bound (using hSigma_le from Step 1):
    have h_upper_bound : (L / (2 * L - 1)) * (sigma ε (ε^(-2 : ℝ) / (-lambda))).rpow (-(2 * L - 1) / L) / (ε^(-2 : ℝ) / (-lambda)) ≤ -lambda + (L / (2 * L - 1)) * (-lambda) * ε^(1 / L : ℝ) + mu * ε^(1 / L : ℝ) := by
      have := neg_branch_v_upper_bound L hL lambda mu hlambda_neg hmu_pos ( sigma ε ) ( fun t ht => hSigma_pos ε hε_pos ( by linarith ) t ht ) ( hSigma_cont ε hε_pos ( by linarith ) ) ( fun t ht => hSigma_ode ε hε_pos ( by linarith ) t ht ) ( fun t ht => neg_branch_sigma_le_init L hL lambda mu hlambda_neg hmu_pos ( sigma ε ) ( fun t ht => hSigma_pos ε hε_pos ( by linarith ) t ht ) ( hSigma_cont ε hε_pos ( by linarith ) ) ( fun t ht => hSigma_ode ε hε_pos ( by linarith ) t ht ) t ht ) ( ε ^ ( -2 : ℝ ) / -lambda ) ( by exact div_pos ( Real.rpow_pos_of_pos hε_pos _ ) ( neg_pos.mpr hlambda_neg ) );
      rw [ div_le_iff₀ ( div_pos ( Real.rpow_pos_of_pos hε_pos _ ) ( neg_pos.mpr hlambda_neg ) ) ];
      convert mul_le_mul_of_nonneg_left this ( show ( 0 : ℝ ) ≤ L / ( 2 * L - 1 ) by exact div_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ) using 1 ; ring;
      rw [ hSigma_init ε hε_pos ( by linarith ) ] ; norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
      rw [ Real.rpow_add hε_pos, Real.rpow_neg hε_pos.le ] ; norm_cast ; norm_num ; ring;
      grind +suggestions;
    -- Since $\varepsilon < 1/3$, we have $|\log \varepsilon| > 1$.
    have h_log_eps : |Real.log ε| > 1 := by
      rw [ abs_of_neg ( Real.log_neg hε_pos ( by linarith ) ) ];
      linarith [ Real.log_le_sub_one_of_pos hε_pos, show Real.log ε < -1 by rw [ Real.log_lt_iff_lt_exp ( by linarith ) ] ; exact Real.exp_neg_one_gt_d9.trans_le' <| by norm_num; linarith ];
    rw [ abs_le ];
    constructor <;> nlinarith [ show 0 < ( L : ℝ ) / ( 2 * L - 1 ) * -lambda * ε ^ ( 1 / ( L : ℝ ) ) by exact mul_pos ( mul_pos ( div_pos ( by positivity ) ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ) ( neg_pos.mpr hlambda_neg ) ) ( Real.rpow_pos_of_pos hε_pos _ ), show 0 < mu * ε ^ ( 1 / ( L : ℝ ) ) by positivity, show 0 < ε ^ ( 1 / ( L : ℝ ) ) by positivity, abs_nonneg ( Real.log ε ), mul_le_mul_of_nonneg_left h_log_eps.le ( show 0 ≤ ε ^ ( 1 / ( L : ℝ ) ) by positivity ) ]

end JepaRhoRecovery