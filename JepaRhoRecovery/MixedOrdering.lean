/-
# JepaRhoRecovery.MixedOrdering

Layer 5.1 — mixed-sign ordering. Once positive features are learned and
negative features are suppressed, JEPA training implicitly partitions the
spectrum into {learn, discard, suppress} in a definite *temporal* order:
positive features finish learning before any negative feature is fully
suppressed, under a gap condition on the signed eigenvalues.
-/

import Mathlib
import JepaRhoRecovery.Basic
import JepaRhoRecovery.SignedODE
import JepaRhoRecovery.Inversion

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §5.1 — Mixed-sign ordering theorem -/

-- ORIGINAL STATEMENT (commented out — unprovable as stated).
--
-- The bounds `tau_pos_bound` and `tau_neg_lower` constrain `tau_pos s epsilon`
-- and `tau_neg r epsilon` only at the specific `epsilon` parameter, but the
-- conclusion quantifies over ALL `ε ∈ (0, eps_max)`.  Without bounds that hold
-- uniformly for all small ε, no information is available about `tau_pos s ε` or
-- `tau_neg r ε` at `ε ≠ epsilon`, making the theorem unprovable.
-- The corrected version below universalizes the bounds to hold for all
-- `ε ∈ (0, 1)`, which is what the Layer 2.2 / 4.1(c) corollaries actually
-- provide.
--
-- theorem mixed_sign_ordering_original
--     (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
--     (L : ℕ) (hL : 2 ≤ L)
--     (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
--     (P N : Finset (Fin d))
--     (hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
--     (hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
--     (hPN_disjoint : Disjoint P N)
--     (hGap : ∀ s ∈ P, ∀ r ∈ N, |(eb.pairs r).rho| < (eb.pairs s).rho)
--     (tau_pos : Fin d → ℝ → ℝ)
--     (tau_pos_bound : ∀ s ∈ P, ∃ K : ℝ, 0 < K ∧
--         tau_pos s epsilon
--           ≤ K / ((eb.pairs s).rho * (eb.pairs s).mu)
--             * Real.rpow epsilon (-(1 : ℝ) / L))
--     (tau_neg : Fin d → ℝ → ℝ)
--     (tau_neg_lower : ∀ r ∈ N, ∃ K : ℝ, 0 < K ∧
--         K / |(eb.pairs r).rho * (eb.pairs r).mu|
--           * Real.rpow epsilon (-(2 * (L : ℝ) - 1) / L)
--             ≤ tau_neg r epsilon)
--     (eps_threshold : ℝ) (heps_thr_pos : 0 < eps_threshold) :
--     ∃ eps_max : ℝ, 0 < eps_max ∧
--       ∀ ε : ℝ, 0 < ε → ε < eps_max →
--         ∀ s ∈ P, ∀ r ∈ N, tau_pos s ε < tau_neg r ε := by
--   sorry

/-! ### Helper lemmas -/

/-
For positive constants `A`, `B` and depth `L ≥ 2`, the term
    `B · ε^{-(2L-1)/L}` eventually dominates `A · ε^{-1/L}` as `ε → 0⁺`.
    The exponent gap is `(2L-2)/L ≥ 1`, so `ε^{(2L-2)/L} → 0` and for
    small enough `ε`, `A · ε^{-1/L} < B · ε^{-(2L-1)/L}`.
-/
private lemma rpow_upper_lt_lower (A B : ℝ) (_hA : 0 < A) (hB : 0 < B)
    (L : ℕ) (hL : 2 ≤ L) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      A * Real.rpow ε (-(1 : ℝ) / L) < B * Real.rpow ε (-(2 * (L : ℝ) - 1) / L) := by
  -- We want to find $\epsilon_0$ such that $A * \epsilon^{-1/L} < B * \epsilon^{-(2L-1)/L}$ for all $\epsilon < \epsilon_0$.
  suffices h_suff : ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ → (A / B) < ε ^ (-(2 * L - 1) / L + 1 / L : ℝ) by
    obtain ⟨ ε₀, hε₀₁, hε₀₂, hε₀₃ ⟩ := h_suff; refine' ⟨ ε₀, hε₀₁, hε₀₂, fun ε hε₁ hε₂ => _ ⟩ ; specialize hε₀₃ ε hε₁ hε₂ ; simp_all +decide [ Real.rpow_def_of_pos, div_eq_mul_inv ] ;
    convert mul_lt_mul_of_pos_left hε₀₃ ( show 0 < B * Real.exp ( - ( Real.log ε * ( L : ℝ ) ⁻¹ ) ) by positivity ) using 1 <;> ring;
    · norm_num [ hB.ne' ];
    · norm_num [ mul_assoc, ← Real.exp_add, ne_of_gt ( zero_lt_two.trans_le hL ) ] ; ring;
      norm_num;
  -- We want to find $\epsilon_0$ such that $(A / B) < \epsilon^{-(2L-2)/L}$ for all $\epsilon < \epsilon_0$.
  suffices h_suff : ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ → (A / B) < ε ^ (-(2 * L - 2) / L : ℝ) by
    convert h_suff using 6 ; ring;
  have h_exp : Filter.Tendsto (fun ε : ℝ => ε ^ (-(2 * L - 2) / L : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have := Real.tendsto_log_nhdsGT_zero;
    have : Filter.Tendsto (fun ε : ℝ => Real.exp ((-(2 * L - 2) / L : ℝ) * Real.log ε)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      exact Real.tendsto_exp_atTop.comp <| Filter.Tendsto.const_mul_atBot_of_neg ( div_neg_of_neg_of_pos ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) <| by positivity ) this;
    exact this.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ Real.rpow_def_of_pos hx, mul_comm ] );
  have := h_exp.eventually_gt_atTop ( A / B );
  rcases ( Metric.mem_nhdsWithin_iff.mp <| this ) with ⟨ ε₀, hε₀, hε₀' ⟩;
  exact ⟨ Min.min ε₀ 1, lt_min hε₀ zero_lt_one, min_le_right _ _, fun ε hε₁ hε₂ => hε₀' ⟨ mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith [ min_le_left ε₀ 1 ], by linarith [ min_le_left ε₀ 1 ] ⟩, hε₁ ⟩ ⟩

/-
Finite intersection of "eventually for small ε" statements over a
    product of two finsets. For each pair `(s, r) ∈ S₁ × S₂`, given
    `ε₀(s,r) > 0`, the minimum over the finite product is still positive.
-/
private lemma finset_forall_eps₂ {ι₁ ι₂ : Type*}
    (S₁ : Finset ι₁) (S₂ : Finset ι₂) (Q : ι₁ → ι₂ → ℝ → Prop)
    (h : ∀ s ∈ S₁, ∀ r ∈ S₂, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Q s r ε) :
    ∃ eps_max : ℝ, 0 < eps_max ∧ ∀ ε : ℝ, 0 < ε → ε < eps_max →
      ∀ s ∈ S₁, ∀ r ∈ S₂, Q s r ε := by
  -- By choosing `ε₀₁(s)` for each `s ∈ S₁` as the minimum of the `ε₀` values from `h` for that `s` and all `r ∈ S₂`, we ensure `∀ r ∈ S₂, ∀ ε, 0 < ε → ε < ε₀₁(s) → Q s r ε`.
  have h_min : ∀ s ∈ S₁, ∃ ε₀₁ : ℝ, (0 < ε₀₁ ∧ ∀ r ∈ S₂, ∀ ε, 0 < ε → ε < ε₀₁ → Q s r ε) := by
    intro s hs
    have h_eps₀ : ∃ ε₀ : ι₂ → ℝ, (∀ r ∈ S₂, 0 < ε₀ r ∧ ∀ ε, 0 < ε → ε < ε₀ r → Q s r ε) := by
      choose! ε₀ hε₀ using h s hs;
      exact ⟨ ε₀, hε₀ ⟩;
    obtain ⟨ε₀, hε₀⟩ := h_eps₀;
    by_cases hS₂ : S₂.Nonempty;
    · exact ⟨ Finset.min' ( S₂.image ε₀ ) ⟨ _, Finset.mem_image_of_mem ε₀ hS₂.choose_spec ⟩, by have := Finset.min'_mem ( S₂.image ε₀ ) ⟨ _, Finset.mem_image_of_mem ε₀ hS₂.choose_spec ⟩ ; aesop, fun r hr ε hε₁ hε₂ => hε₀ r hr |>.2 ε hε₁ ( lt_of_lt_of_le hε₂ ( Finset.min'_le _ _ ( Finset.mem_image_of_mem ε₀ hr ) ) ) ⟩;
    · exact ⟨ 1, zero_lt_one, fun r hr => False.elim <| hS₂ ⟨ r, hr ⟩ ⟩;
  choose! ε₀₁ hε₀₁_pos hε₀₁ using h_min;
  by_cases hS₁ : S₁.Nonempty;
  · exact ⟨ Finset.min' ( S₁.image ε₀₁ ) ⟨ _, Finset.mem_image_of_mem ε₀₁ hS₁.choose_spec ⟩, by have := Finset.min'_mem ( S₁.image ε₀₁ ) ⟨ _, Finset.mem_image_of_mem ε₀₁ hS₁.choose_spec ⟩ ; aesop, fun ε hε₁ hε₂ s hs r hr => hε₀₁ s hs r hr ε hε₁ ( lt_of_lt_of_le hε₂ ( Finset.min'_le _ _ ( Finset.mem_image_of_mem ε₀₁ hs ) ) ) ⟩;
  · exact ⟨ 1, zero_lt_one, fun ε hε₁ hε₂ s hs r hr => False.elim <| hS₁ ⟨ s, hs ⟩ ⟩

/-! ### Main theorem (corrected) -/

/-
**Theorem 5.1 (Mixed-sign ordering — corrected).**

    Same statement as the original `mixed_sign_ordering`, but with the
    time bounds universalized to hold for all `ε ∈ (0, 1)` (matching
    what the Layer 2.2 / 4.1(c) corollaries actually produce).

    Modifications from original:
    • Removed `epsilon`, `heps_pos`, `heps_small` (no longer needed).
    • `tau_pos_bound` now quantifies over all `ε ∈ (0, 1)`.
    • `tau_neg_lower` now quantifies over all `ε ∈ (0, 1)`.
    • Removed `eps_threshold`, `heps_thr_pos` (unused in original).
-/
theorem mixed_sign_ordering
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (P N : Finset (Fin d))
    (hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
    (hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
    (_hPN_disjoint : Disjoint P N)
    (_hGap : ∀ s ∈ P, ∀ r ∈ N, |(eb.pairs r).rho| < (eb.pairs s).rho)
    (tau_pos : Fin d → ℝ → ℝ)
    (tau_pos_bound : ∀ s ∈ P, ∃ K : ℝ, 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
        tau_pos s ε
          ≤ K / ((eb.pairs s).rho * (eb.pairs s).mu)
            * Real.rpow ε (-(1 : ℝ) / L))
    (tau_neg : Fin d → ℝ → ℝ)
    (tau_neg_lower : ∀ r ∈ N, ∃ K : ℝ, 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
        K / |(eb.pairs r).rho * (eb.pairs r).mu|
          * Real.rpow ε (-(2 * (L : ℝ) - 1) / L)
            ≤ tau_neg r ε) :
    ∃ eps_max : ℝ, 0 < eps_max ∧
      ∀ ε : ℝ, 0 < ε → ε < eps_max →
        ∀ s ∈ P, ∀ r ∈ N, tau_pos s ε < tau_neg r ε := by
  have h_rpow_upper_lt_lower : ∀ s ∈ P, ∀ r ∈ N, ∃ eps_max : ℝ, 0 < eps_max ∧ eps_max ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < eps_max → tau_pos s ε < tau_neg r ε := by
    intros s hs r hr
    obtain ⟨K_pos, hK_pos_pos, hK_pos_bound⟩ := tau_pos_bound s hs
    obtain ⟨K_neg, hK_neg_pos, hK_neg_bound⟩ := tau_neg_lower r hr
    have h_rpow_upper_lt_lower : ∃ eps_max : ℝ, 0 < eps_max ∧ eps_max ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < eps_max → (K_pos / ((eb.pairs s).rho * (eb.pairs s).mu)) * ε.rpow (-1 / L : ℝ) < (K_neg / abs ((eb.pairs r).rho * (eb.pairs r).mu)) * ε.rpow (-(2 * L - 1) / L : ℝ) := by
      convert rpow_upper_lt_lower ( K_pos / ( ( eb.pairs s |> SignedGenEigenpair.rho ) * ( eb.pairs s |> SignedGenEigenpair.mu ) ) ) ( K_neg / |( eb.pairs r |> SignedGenEigenpair.rho ) * ( eb.pairs r |> SignedGenEigenpair.mu )| ) _ _ L hL using 1;
      · exact div_pos hK_pos_pos ( mul_pos ( hP s hs ) ( by linarith [ ( eb.pairs s ).hmu_pos ] ) );
      · exact div_pos hK_neg_pos ( abs_pos.mpr ( mul_ne_zero ( ne_of_lt ( hN r hr ) ) ( ne_of_gt ( eb.pairs r |>.hmu_pos ) ) ) );
    exact ⟨ h_rpow_upper_lt_lower.choose, h_rpow_upper_lt_lower.choose_spec.1, h_rpow_upper_lt_lower.choose_spec.2.1, fun ε hε₁ hε₂ => lt_of_le_of_lt ( hK_pos_bound ε hε₁ ( hε₂.trans_le h_rpow_upper_lt_lower.choose_spec.2.1 ) ) ( lt_of_lt_of_le ( h_rpow_upper_lt_lower.choose_spec.2.2 ε hε₁ hε₂ ) ( hK_neg_bound ε hε₁ ( hε₂.trans_le h_rpow_upper_lt_lower.choose_spec.2.1 ) ) ) ⟩;
  obtain ⟨eps_max, h_eps_max⟩ : ∃ eps_max : ℝ, 0 < eps_max ∧ ∀ s ∈ P, ∀ r ∈ N, ∀ ε : ℝ, 0 < ε → ε < eps_max → tau_pos s ε < tau_neg r ε := by
    have h_finite : ∃ eps_max : ℝ, 0 < eps_max ∧ ∀ s ∈ P, ∀ r ∈ N, ∀ ε : ℝ, 0 < ε → ε < eps_max → tau_pos s ε < tau_neg r ε := by
      have := finset_forall_eps₂ P N (fun s r ε => tau_pos s ε < tau_neg r ε) (fun s hs r hr => by
        exact Exists.elim ( h_rpow_upper_lt_lower s hs r hr ) fun ε₀ hε₀ => ⟨ ε₀, hε₀.1, fun ε hε₁ hε₂ => hε₀.2.2 ε hε₁ hε₂ ⟩)
      exact ⟨ this.choose, this.choose_spec.1, fun s hs r hr ε hε₁ hε₂ => this.choose_spec.2 ε hε₁ hε₂ s hs r hr ⟩
    exact h_finite;
  exact ⟨ eps_max, h_eps_max.1, fun ε hε₁ hε₂ s hs r hr => h_eps_max.2 s hs r hr ε hε₁ hε₂ ⟩

end JepaRhoRecovery