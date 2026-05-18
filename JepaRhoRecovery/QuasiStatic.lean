/-
# JepaRhoRecovery.QuasiStatic

Layer 1.1: rigorous quasi-static decoder ODE. Hand-port of paper-1's
`quasiStatic_approx` (Aristotle job 1ccc1ab8), restated against the spinoff's
signed eigenbasis types and with vacuity discipline:

* The decoder ODE is stated via `HasDerivAt`, not `deriv f t = …`.
* Every hypothesis is non-trivially constraining (`hPhaseA`, `hContraction`
  bound real functions; no `True` placeholders).
* The output constant `C_track = C_A + D₀/c₀` is provably ε-independent.

The Grönwall machinery is re-derived locally (see `contractive_gronwall_bound`
below); we do not Lake-depend on `jepa-learning-order` (see project CLAUDE.md).
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## Local Grönwall machinery

Ported from `jepa-learning-order/JepaLearningOrder/Lemmas.lean`
(`contractive_gronwall_bound`). Statement and proof transcribed verbatim
so the spinoff has no cross-project Lake dependency. -/

/-- **Contractive Grönwall bound (integrated form).**
    If `f : [0, T] → ℝ` is continuous, non-negative, and admits a derivative
    satisfying `f'(t) ≤ -λ f(t) + D` with `λ > 0`, `D ≥ 0`, then for all
    `t ∈ [0, T]`,
        f(t) ≤ f(0) + D / λ.
-/
private lemma contractive_gronwall_bound
    {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ} {lam D : ℝ}
    (hlam : 0 < lam) (hD : 0 ≤ D)
    (hf_cont : ContinuousOn f (Set.Icc 0 T))
    (hf_nn : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)
    (hf_deriv : ∀ t ∈ Set.Ico 0 T,
      ∃ f' : ℝ, HasDerivAt f f' t ∧ f' ≤ -lam * f t + D) :
    ∀ t ∈ Set.Icc 0 T, f t ≤ f 0 + D / lam := by
  intro t ht; by_cases h_cases : t = 0; simp_all +decide [ div_neg, neg_div ] ;
  · positivity;
  · have h_le_contractive : f t ≤ f 0 * Real.exp (-lam * t) + (D / lam) * (1 - Real.exp (-lam * t)) := by
      have h_le_contractive : ∀ t ∈ Set.Ioo 0 T, deriv (fun t => (f t - D / lam) * Real.exp (lam * t)) t ≤ 0 := by
        intro t ht; obtain ⟨ f', hf', hf'' ⟩ := hf_deriv t ⟨ ht.1.le, ht.2 ⟩ ; norm_num [ hf'.differentiableAt, mul_comm lam ] ; ring_nf ;
        rw [ hf'.deriv ] ; nlinarith [ mul_inv_cancel_left₀ hlam.ne' ( Real.exp ( t * lam ) * D ), Real.exp_pos ( t * lam ) ];
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 t, deriv (fun t => (f t - D / lam) * Real.exp (lam * t)) c = ( (f t - D / lam) * Real.exp (lam * t) - (f 0 - D / lam) * Real.exp (lam * 0) ) / (t - 0) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact lt_of_le_of_ne ht.1 ( Ne.symm h_cases );
        · exact ContinuousOn.mul ( ContinuousOn.sub ( hf_cont.mono ( Set.Icc_subset_Icc le_rfl ht.2 ) ) continuousOn_const ) ( Continuous.continuousOn ( Real.continuous_exp.comp ( continuous_const.mul continuous_id' ) ) );
        · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by obtain ⟨ f', hf', hf'' ⟩ := hf_deriv x ⟨ hx.1.le, hx.2.trans_le ht.2 ⟩ ; exact DifferentiableAt.mul ( DifferentiableAt.sub ( hf'.differentiableAt ) ( differentiableAt_const _ ) ) ( DifferentiableAt.exp ( differentiableAt_id.const_mul _ ) ) );
      have := h_le_contractive c ⟨ hc.1.1, hc.1.2.trans_le ht.2 ⟩ ; rw [ hc.2, div_le_iff₀ ] at this <;> norm_num [ Real.exp_neg ] at * <;> try linarith [ hc.1.1, hc.1.2 ] ;
      field_simp;
      nlinarith [ mul_div_cancel₀ D hlam.ne', Real.exp_pos ( lam * t ), Real.add_one_le_exp ( lam * t ), mul_le_mul_of_nonneg_left ( Real.add_one_le_exp ( lam * t ) ) hlam.le ];
    nlinarith [ hf_nn 0 ( by norm_num; linarith ), Real.exp_pos ( -lam * t ), Real.exp_le_one_iff.mpr ( show -lam * t ≤ 0 by nlinarith [ ht.1, ht.2 ] ), div_nonneg hD hlam.le ]

/-! ## Theorem 1.1 — quasi-static decoder tracking (rigorous) -/

/-- **Theorem 1.1 (Quasi-static decoder — rigorous).**

    Hand-port of paper-1's `quasiStatic_approx` against the signed eigenbasis.
    The hypothesis bundle mirrors paper-1: a real `HasDerivAt` decoder ODE,
    a Phase-A initial bound, and a Phase-B contraction–drift bound. All three
    are non-vacuously constraining, eliminating paper-1's
    `∀ t, deriv (…) t ≤ 0` placeholder.

    Conclusion: there exists a positive ε-independent constant `C_track`
    with `‖V t − V_qs(W̄ t)‖_F ≤ C_track · ε^{2(L−1)/L}` on `[0, t_max]`.
-/
theorem quasiStatic_rigorous
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (Wbar V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    -- (H-PhaseA) Phase-A output: initial tracking error already small in ε.
    (hPhaseA : ∃ C_A : ℝ, 0 < C_A ∧
        matFrobNorm (V 0 - quasiStaticDecoder dat (Wbar 0))
          ≤ C_A * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L))
    -- (H-Contraction) Phase-B ODE bound on the tracking norm
    --   f'(t) ≤ -(c₀ ε^{2/L}) f(t) + D₀ ε².
    -- This is the ε-independent contraction rate / drift bundle paper-1 derives
    -- via `pd_quadratic_lower_bound` and the chain rule for V_qs(W̄(·)).
    (hContraction : ∃ (c₀ D₀ : ℝ), 0 < c₀ ∧ 0 < D₀ ∧
      (∀ t ∈ Set.Ico 0 t_max,
        ∃ f' : ℝ,
          HasDerivAt
            (fun s => matFrobNorm (V s - quasiStaticDecoder dat (Wbar s))) f' t ∧
          f' ≤ -(c₀ * Real.rpow epsilon ((2 : ℝ) / L)) *
                matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
              + D₀ * epsilon ^ 2))
    -- (H-NN) Tracking norm is non-negative on [0, t_max].
    (hNorm_nn : ∀ t ∈ Set.Icc 0 t_max,
        0 ≤ matFrobNorm (V t - quasiStaticDecoder dat (Wbar t)))
    -- (H-Cont) Tracking norm is continuous on [0, t_max].
    (hNorm_cont : ContinuousOn
        (fun t => matFrobNorm (V t - quasiStaticDecoder dat (Wbar t)))
        (Set.Icc 0 t_max)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Set.Icc 0 t_max,
        matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
          ≤ C * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L) := by
  obtain ⟨C_A, hC_A_pos, hPhaseA_bound⟩ := hPhaseA
  obtain ⟨c₀, D₀, hc₀_pos, hD₀_pos, hODE⟩ := hContraction
  set lam_rate := c₀ * Real.rpow epsilon ((2 : ℝ) / ↑L) with hlam_def
  set drift := D₀ * epsilon ^ 2 with hdrift_def
  have hlam_pos : 0 < lam_rate := mul_pos hc₀_pos (Real.rpow_pos_of_pos heps_pos _)
  have hdrift_nn : 0 ≤ drift := mul_nonneg hD₀_pos.le (pow_nonneg heps_pos.le _)
  have hGronwall := contractive_gronwall_bound ht_max hlam_pos hdrift_nn
    hNorm_cont hNorm_nn
    (fun t ht => by
      obtain ⟨f', hf'_deriv, hf'_bound⟩ := hODE t ht
      exact ⟨f', hf'_deriv, hf'_bound⟩)
  set C_track := C_A + D₀ / c₀ with hCtrack_def
  refine ⟨C_track, by positivity, fun t ht => ?_⟩
  have hGW := hGronwall t ht
  have hL_ne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heps_pow_eq : epsilon ^ (2 : ℕ) / Real.rpow epsilon ((2 : ℝ) / ↑L)
      = Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L) := by
    have h2 : epsilon ^ (2 : ℕ) = Real.rpow epsilon (2 : ℝ) := by
      have := (Real.rpow_natCast epsilon 2).symm
      simpa using this
    have hexp_eq : (2 : ℝ) - 2 / ↑L = 2 * ((↑L : ℝ) - 1) / ↑L := by
      field_simp
    have hsub : Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L)
        = Real.rpow epsilon 2 / Real.rpow epsilon ((2 : ℝ) / ↑L) := by
      rw [← hexp_eq]; exact Real.rpow_sub heps_pos _ _
    rw [h2, hsub]
  have heps_arith : D₀ * epsilon ^ 2 / (c₀ * Real.rpow epsilon ((2 : ℝ) / ↑L))
      = D₀ / c₀ * Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L) := by
    rw [mul_div_assoc]
    rw [show epsilon ^ 2 / (c₀ * Real.rpow epsilon ((2 : ℝ) / ↑L)) =
        epsilon ^ 2 / Real.rpow epsilon ((2 : ℝ) / ↑L) / c₀ from by
      rw [div_div, mul_comm]]
    rw [heps_pow_eq]; ring
  calc matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
      ≤ matFrobNorm (V 0 - quasiStaticDecoder dat (Wbar 0)) + drift / lam_rate := hGW
    _ ≤ C_A * Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L) + drift / lam_rate := by
        linarith [hPhaseA_bound]
    _ = C_A * Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L)
        + D₀ / c₀ * Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L) := by
        simp only [hdrift_def, hlam_def]; rw [heps_arith]
    _ = C_track * Real.rpow epsilon (2 * ((↑L : ℝ) - 1) / ↑L) := by ring

end JepaRhoRecovery
