/-
# JepaRhoRecovery.FiniteSample

Layer 3.2 — end-to-end finite-sample rate. Combines Layer 3.1
(sample-covariance perturbation of `ρ_r*`) with Layer 2.2 (inversion
formula) to bound the estimator error
`|ρ̂_r − ρ_r*|` by `O(ε^{1/L} |log ε| + n^{-1/2})` for sub-Gaussian
data, where the `n^{-1/2}` arises from operator-norm matrix concentration
via matrix Bernstein.

The concentration rate `δ(n) = O(n^{-1/2})` is taken as a hypothesis
(matrix Bernstein for sub-Gaussian distributions is established in the
statistics literature but only partially in Mathlib).
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import JepaRhoRecovery.Basic
import JepaRhoRecovery.SampleNoise
import JepaRhoRecovery.Inversion
import JepaRhoRecovery.PlateauEstimator
import JepaRhoRecovery.SignedRecovery
import JepaRhoRecovery.MixedOrdering

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §3.2 — End-to-end finite-sample rate -/

/-- **Theorem 3.2 (Finite-sample rate for ρ̂_r — positive branch).**

    For a feature with `ρ_r* > 0`, the inversion estimator from the
    *sample* trajectory satisfies, with probability at least `1 − ν`,

        |ρ̂_r − ρ_r*| ≤ C_+ · ε^{1/L} |log ε|  +  C_n · √(log(1/ν) / n),

    where `C_+ = C_+(ρ_r*, L)` is the deterministic-ε constant from
    Layer 2.2 and `C_n` absorbs the matrix-concentration constants from
    Layer 3.1.

    Stated abstractly: given a sample-side Laurent-expansion hypothesis
    (the sample trajectory satisfies the same `h_laurent` bound, with the
    *sample* `ρ̂_r* := λ̂_r* / μ̂_r` in place of the population quantity),
    combine the Layer-2.2 deterministic bound with the Layer-3.1
    perturbation bound via triangle inequality.

    PROVIDED SOLUTION
    Step 1. Apply `JepaRhoRecovery.Inversion.rho_hat_rate` to the sample
    trajectory, yielding `|rho_sample_hat ε − ρ̂_r*| ≤ C_+ ε^{1/L} |log ε|`.
    Step 2. Apply `sample_eigenvalue_perturbation` (Layer 3.1) to bound
    `|ρ̂_r* − ρ_r*| ≤ C · (δ_x + δ_y)`.
    Step 3. Matrix Bernstein gives `δ_x, δ_y = O(√(log(1/ν) / n))` with
    probability `≥ 1 − ν` (taken as hypothesis `h_conc`).
    Step 4. Triangle:
    `|rho_sample_hat ε − ρ_r*| ≤ C_+ ε^{1/L} |log ε| + C·(δ_x + δ_y)`.
-/
theorem finite_sample_rate_pos
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d) (_hrho_pos : 0 < (eb.pairs r).rho)
    -- Sample-side hitting time satisfies a Laurent expansion.
    (t_crit_hat : ℝ → ℝ)
    (rho_hat_pop : ℝ)  -- population-side sample-eigenvalue estimate ρ̂_r*
    (hrho_hat_pop_pos : 0 < rho_hat_pop)  -- spec fix: needed for inversion
    (K_log : ℝ) (hK_log_pos : 0 < K_log)
    (h_laurent_sample : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_crit_hat ε
        - (1 / (rho_hat_pop * (eb.pairs r).mu)) *
            ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
              (L : ℝ) / ((n : ℝ) * rho_hat_pop ^ (2 * L - n - 1))
                * ε ^ (((n : ℝ) - 2) / (L : ℝ))|
        ≤ K_log * |Real.log ε|)
    -- Sample-eigenvalue perturbation (Layer 3.1 output).
    (delta_n : ℝ) (hδn_pos : 0 < delta_n)
    (h_perturbation : |rho_hat_pop - (eb.pairs r).rho| ≤ delta_n) :
    -- Spec: existential ε_max (was global on (0, exp(-1)) before — that
    -- shape isn't achievable since rho_hat_rate's bound is only valid
    -- below an internal ε_0 threshold).
    ∃ (rho_estimator : ℝ → ℝ) (eps_max C_eps C_n : ℝ),
        0 < eps_max ∧ 0 < C_eps ∧ 0 < C_n ∧
      ∀ ε : ℝ, 0 < ε → ε < eps_max →
        |rho_estimator ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_n * delta_n := by
  -- Step 1: invoke rho_hat_rate to get the inversion estimator.
  set lambda : ℝ := rho_hat_pop * (eb.pairs r).mu with hlam_def
  have hlam_pos : 0 < lambda :=
    mul_pos hrho_hat_pop_pos (eb.pairs r).hmu_pos
  obtain ⟨ε_0, C_rho, hε_0_pos, _hε_0_lt_one, hC_rho_pos, hbound⟩ :=
    JepaRhoRecovery.rho_hat_rate L hL lambda rho_hat_pop hrho_hat_pop_pos hlam_pos
      t_crit_hat K_log hK_log_pos
      (by intro ε hε_pos hε_lt; simpa [hlam_def] using h_laurent_sample ε hε_pos hε_lt)
  -- Step 2: define the estimator as the inversion formula.
  refine ⟨fun ε => ((L : ℝ) / (lambda * t_crit_hat ε * ε ^ ((1 : ℝ) / L)))
              ^ ((1 : ℝ) / (2 * (L : ℝ) - 2)),
          ε_0, C_rho, 1, hε_0_pos, hC_rho_pos, zero_lt_one, ?_⟩
  intro ε hε_pos hε_lt
  -- Step 3: triangle inequality.
  -- |rho_est ε - rho_pop| ≤ |rho_est ε - rho_hat_pop| + |rho_hat_pop - rho_pop|
  --                       ≤ C_rho · ε^(1/L) · |log ε| + delta_n
  have h_rho_est := hbound ε hε_pos hε_lt
  have h_triangle :
      |((L : ℝ) / (lambda * t_crit_hat ε * ε ^ ((1 : ℝ) / L))) ^
            ((1 : ℝ) / (2 * (L : ℝ) - 2)) - (eb.pairs r).rho|
        ≤ |((L : ℝ) / (lambda * t_crit_hat ε * ε ^ ((1 : ℝ) / L))) ^
              ((1 : ℝ) / (2 * (L : ℝ) - 2)) - rho_hat_pop|
          + |rho_hat_pop - (eb.pairs r).rho| :=
    abs_sub_le _ _ _
  calc |((L : ℝ) / (lambda * t_crit_hat ε * ε ^ ((1 : ℝ) / L))) ^
            ((1 : ℝ) / (2 * (L : ℝ) - 2)) - (eb.pairs r).rho|
      ≤ |((L : ℝ) / (lambda * t_crit_hat ε * ε ^ ((1 : ℝ) / L))) ^
              ((1 : ℝ) / (2 * (L : ℝ) - 2)) - rho_hat_pop|
        + |rho_hat_pop - (eb.pairs r).rho| := h_triangle
    _ ≤ C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n :=
        add_le_add h_rho_est h_perturbation
    _ = C_rho * ε ^ ((1 : ℝ) / L) * |Real.log ε| + 1 * delta_n := by ring

/-! ## §3.2-neg — Negative-branch finite-sample rate (Fix 2)

    Mirrors `finite_sample_rate_pos` but for `ρ_r* < 0`. Directly wraps
    `SignedRecovery.signed_recovery_neg_magnitude_jepa` (Fix 1's
    composition of the trajectory-derived λ̂-rate with an ordinary
    μ̂-concentration bound), instantiated at `λ := ρ_r*·μ_r` so that
    `λ/μ_r = ρ_r*`. Unlike the positive branch, the sample-noise input
    here (`delta_mu`, the μ̂-concentration radius) is not a separate
    Layer-3.1 perturbation bound bolted on afterwards — it is *the*
    mechanism by which the negative branch escapes the Layer-4.2(iii)
    sign-only obstruction, so it appears already inside the composed
    bound rather than as an additive Layer-3.1 correction. -/

/-- **Theorem 3.2-neg (Finite-sample rate for ρ̂_r — negative branch, Fix 2).**

    For a feature with `ρ_r* < 0`, the delta-method estimator from
    `signed_recovery_neg_magnitude_jepa` satisfies, for ε small enough,

        |ρ̂_r − ρ_r*| ≤ C_eps · ε^{1/L} |log ε| + C_n · delta_mu,

    where `delta_mu` is the μ̂-concentration radius and `C_eps = C_n` is
    the constant produced by the trajectory/λ̂-rate + μ̂-concentration
    composition (kept as two named constants only to match
    `finite_sample_rate_pos`'s interface). -/
theorem finite_sample_rate_neg
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d) (hrho_neg : (eb.pairs r).rho < 0)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        ((eb.pairs r).rho * (eb.pairs r).mu * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - (eb.pairs r).mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε)
    -- Sample-covariance concentration bound on μ̂ (see Fix 1 header note
    -- in `SignedRecovery.lean`).
    (mu_hat : ℝ) (delta_mu : ℝ) (hδmu_nonneg : 0 ≤ delta_mu)
    (hδmu_small : delta_mu < (eb.pairs r).mu / 2)
    (h_mu_conc : |mu_hat - (eb.pairs r).mu| ≤ delta_mu) :
    ∃ (rho_estimator : ℝ → ℝ) (eps_max C_eps C_n : ℝ),
        0 < eps_max ∧ 0 < C_eps ∧ 0 < C_n ∧
      ∀ ε : ℝ, 0 < ε → ε < eps_max →
        |rho_estimator ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_n * delta_mu := by
  have hlambda_neg : (eb.pairs r).rho * (eb.pairs r).mu < 0 :=
    mul_neg_of_neg_of_pos hrho_neg (eb.pairs r).hmu_pos
  obtain ⟨rho_hat, eps_0, C, hε0_pos, _hε0_lt1, hC_pos, hbound⟩ :=
    signed_recovery_neg_magnitude_jepa L hL ((eb.pairs r).rho * (eb.pairs r).mu)
      (eb.pairs r).mu hlambda_neg (eb.pairs r).hmu_pos
      sigma hSigma_pos hSigma_cont hSigma_ode hSigma_init
      mu_hat delta_mu hδmu_nonneg hδmu_small h_mu_conc
  refine ⟨rho_hat, eps_0, C, C, hε0_pos, hC_pos, hC_pos, ?_⟩
  intro ε hε_pos hε_lt
  have heq : (eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).mu = (eb.pairs r).rho := by
    field_simp [(eb.pairs r).hmu_pos.ne']
  have h := hbound ε hε_pos hε_lt
  rwa [heq] at h

/-! ## §3.2-e2e — End-to-end finite-sample rate, all three branches (Fix 2)

    Generalises `finite_sample_rate_pos`/`finite_sample_rate_neg` from a
    single feature to a `Finset`-uniform threshold across the whole
    signed spectrum `P ∪ N ∪ {ρ* = 0}`, exactly the way `Main.
    signed_decomposition` bundles the trajectory-only rates. This is
    the theorem the paper's crosswalk cites as covering all three
    branches of the finite-sample rate. -/

/-- **Theorem (End-to-end finite-sample rate, all three branches).**

    Given per-feature finite-sample bounds for `r ∈ P` (Layer 3.2,
    e.g. from `finite_sample_rate_pos`) and `r ∈ N` (Fix 2, e.g. from
    `finite_sample_rate_neg`), plus exact recovery on the kernel
    (`ρ_r* = 0`), there is a single positive threshold `eps_max` and
    constant `C_eps` such that, for every `ε ∈ (0, eps_max)`:

      * `|ρ̂_r − ρ_r*| ≤ C_eps·ε^{1/L}|log ε| + C_eps·delta_n r` for `r ∈ P`;
      * `|ρ̂_r − ρ_r*| ≤ C_eps·ε^{1/L}|log ε| + C_eps·delta_n r` for `r ∈ N`;
      * `ρ̂_r = 0` whenever `ρ_r* = 0`.

    **Proof.** Same uniform-`C_eps`/`finset_forall_eps₂` reduction as
    `Main.signed_decomposition`'s Fix-1 extension, specialised to the
    two-term finite-sample shape and pooled over `P ∪ N`. -/
theorem end_to_end_rate
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (_hL : 2 ≤ L)
    (P N : Finset (Fin d))
    (_hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
    (_hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
    (hPN_disjoint : Disjoint P N)
    (rho_hat : Fin d → ℝ → ℝ)
    (delta_n : Fin d → ℝ) (hδn_nonneg : ∀ r, 0 ≤ delta_n r)
    -- Positive branch: per-feature finite-sample bound (e.g. discharged
    -- by `finite_sample_rate_pos`).
    (h_pos : ∀ r ∈ P, ∃ ε_0 C : ℝ, 0 < ε_0 ∧ 0 < C ∧
        ∀ ε, 0 < ε → ε < ε_0 →
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C * delta_n r)
    -- Negative branch: per-feature finite-sample bound (Fix 2; e.g.
    -- discharged by `finite_sample_rate_neg`).
    (h_neg : ∀ r ∈ N, ∃ ε_0 C : ℝ, 0 < ε_0 ∧ 0 < C ∧
        ∀ ε, 0 < ε → ε < ε_0 →
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C * delta_n r)
    -- Zero branch: exact — ρ* = 0 forces the estimator to vanish
    -- identically (no trajectory or sample-noise term to bound).
    (h_zero : ∀ r : Fin d, (eb.pairs r).rho = 0 →
        ∀ ε, 0 < ε → ε < 1 → rho_hat r ε = 0) :
    ∃ eps_max C_eps : ℝ, 0 < eps_max ∧ 0 < C_eps ∧
      ∀ ε, 0 < ε → ε < eps_max →
        (∀ r ∈ P, |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r) ∧
        (∀ r ∈ N, |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r) ∧
        (∀ r : Fin d, (eb.pairs r).rho = 0 → rho_hat r ε = 0) := by
  classical
  let C_per : Fin d → ℝ :=
    fun r => if hr : r ∈ P then (h_pos r hr).choose_spec.choose
      else if hr' : r ∈ N then (h_neg r hr').choose_spec.choose
      else 0
  have hC_per_nonneg : ∀ r : Fin d, 0 ≤ C_per r := by
    intro r
    by_cases hr : r ∈ P
    · simp only [C_per, dif_pos hr]
      exact (h_pos r hr).choose_spec.choose_spec.2.1.le
    · by_cases hr' : r ∈ N
      · simp only [C_per, dif_neg hr, dif_pos hr']
        exact (h_neg r hr').choose_spec.choose_spec.2.1.le
      · simp [C_per, dif_neg hr, dif_neg hr']
  set C_eps : ℝ := 1 + (∑ r ∈ P, C_per r) + (∑ r ∈ N, C_per r) with hC_eps_def
  have hC_eps_pos : 0 < C_eps := by
    have h1 : 0 ≤ ∑ r ∈ P, C_per r := Finset.sum_nonneg (fun s _ => hC_per_nonneg s)
    have h2 : 0 ≤ ∑ r ∈ N, C_per r := Finset.sum_nonneg (fun s _ => hC_per_nonneg s)
    simp only [hC_eps_def]; linarith
  have hC_per_dominates_P : ∀ r ∈ P, C_per r ≤ C_eps := by
    intro r hr
    have h_sum_nn_N : 0 ≤ ∑ s ∈ N, C_per s := Finset.sum_nonneg (fun s _ => hC_per_nonneg s)
    have h_le : C_per r ≤ ∑ s ∈ P, C_per s := by
      have hsub : ({r} : Finset (Fin d)) ⊆ P := Finset.singleton_subset_iff.mpr hr
      calc C_per r = ∑ s ∈ ({r} : Finset (Fin d)), C_per s := by simp
        _ ≤ ∑ s ∈ P, C_per s := Finset.sum_le_sum_of_subset_of_nonneg hsub
                                  (fun s _ _ => hC_per_nonneg s)
    simp only [hC_eps_def]; linarith
  have hC_per_dominates_N : ∀ r ∈ N, C_per r ≤ C_eps := by
    intro r hr
    have h_sum_nn_P : 0 ≤ ∑ s ∈ P, C_per s := Finset.sum_nonneg (fun s _ => hC_per_nonneg s)
    have h_le : C_per r ≤ ∑ s ∈ N, C_per s := by
      have hsub : ({r} : Finset (Fin d)) ⊆ N := Finset.singleton_subset_iff.mpr hr
      calc C_per r = ∑ s ∈ ({r} : Finset (Fin d)), C_per s := by simp
        _ ≤ ∑ s ∈ N, C_per s := Finset.sum_le_sum_of_subset_of_nonneg hsub
                                  (fun s _ _ => hC_per_nonneg s)
    simp only [hC_eps_def]; linarith
  obtain ⟨ε_pos, hε_pos_pos, h_pos_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ P,
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ P ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε =>
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r)
        (fun r hr _ _ => by
          refine ⟨(h_pos r hr).choose, ?_, ?_⟩
          · exact (h_pos r hr).choose_spec.choose_spec.1
          · intro ε hε_pos hε_lt
            have hC_r_bound := (h_pos r hr).choose_spec.choose_spec.2.2 ε hε_pos hε_lt
            have hC_r_eq : (h_pos r hr).choose_spec.choose = C_per r := by
              simp [C_per, dif_pos hr]
            rw [hC_r_eq] at hC_r_bound
            have hC_r_le : C_per r ≤ C_eps := hC_per_dominates_P r hr
            have h_rpow_nn : 0 ≤ ε ^ ((1 : ℝ) / L) := Real.rpow_nonneg hε_pos.le _
            have h_log_nn : 0 ≤ |Real.log ε| := abs_nonneg _
            have h_factor_nn : 0 ≤ ε ^ ((1 : ℝ) / L) * |Real.log ε| :=
              mul_nonneg h_rpow_nn h_log_nn
            have hδ_nn : 0 ≤ delta_n r := hδn_nonneg r
            have h1 := mul_le_mul_of_nonneg_right hC_r_le h_factor_nn
            have h2 := mul_le_mul_of_nonneg_right hC_r_le hδ_nn
            nlinarith [hC_r_bound, h1, h2])
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  obtain ⟨ε_neg, hε_neg_pos, h_neg_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ N,
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ N ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε =>
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_n r)
        (fun r hr _ _ => by
          have hrnP : r ∉ P := fun hrP => absurd hr (Finset.disjoint_left.mp hPN_disjoint hrP)
          refine ⟨(h_neg r hr).choose, ?_, ?_⟩
          · exact (h_neg r hr).choose_spec.choose_spec.1
          · intro ε hε_pos hε_lt
            have hC_r_bound := (h_neg r hr).choose_spec.choose_spec.2.2 ε hε_pos hε_lt
            have hC_r_eq : (h_neg r hr).choose_spec.choose = C_per r := by
              simp only [C_per, dif_neg hrnP, dif_pos hr]
            rw [hC_r_eq] at hC_r_bound
            have hC_r_le : C_per r ≤ C_eps := hC_per_dominates_N r hr
            have h_rpow_nn : 0 ≤ ε ^ ((1 : ℝ) / L) := Real.rpow_nonneg hε_pos.le _
            have h_log_nn : 0 ≤ |Real.log ε| := abs_nonneg _
            have h_factor_nn : 0 ≤ ε ^ ((1 : ℝ) / L) * |Real.log ε| :=
              mul_nonneg h_rpow_nn h_log_nn
            have hδ_nn : 0 ≤ delta_n r := hδn_nonneg r
            have h1 := mul_le_mul_of_nonneg_right hC_r_le h_factor_nn
            have h2 := mul_le_mul_of_nonneg_right hC_r_le hδ_nn
            nlinarith [hC_r_bound, h1, h2])
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  refine ⟨min (min ε_pos ε_neg) 1, C_eps,
          lt_min (lt_min hε_pos_pos hε_neg_pos) zero_lt_one, hC_eps_pos, ?_⟩
  intro ε hε_pos hε_lt
  have hε_lt_pos : ε < ε_pos :=
    lt_of_lt_of_le hε_lt (le_trans (min_le_left _ 1) (min_le_left _ _))
  have hε_lt_neg : ε < ε_neg :=
    lt_of_lt_of_le hε_lt (le_trans (min_le_left _ 1) (min_le_right _ _))
  have hε_lt_one : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  exact ⟨h_pos_unif ε hε_pos hε_lt_pos, h_neg_unif ε hε_pos hε_lt_neg,
         fun r hrho_zero => h_zero r hrho_zero ε hε_pos hε_lt_one⟩

/-! ## §3.2′ — Plateau-path finite-sample rate (paper-2 headline)

    Mirrors `finite_sample_rate_pos` but uses the plateau estimator
    (paper-2 framing) instead of the inversion estimator (paper-1
    framing). The deterministic-ε rate carries the same `ε^{1/L}|log ε|`
    asymptotic; the sample-noise contribution carries the same `δ_n`
    additive penalty from Layer 3.1.

    **Probabilistic interpretation.** Under sub-Gaussian data, matrix
    Bernstein gives `δ_n = O(√(log(1/ν)/n))` on an event of probability
    `≥ 1 − ν`. Wiring to `MeasureTheory.ProbabilityMeasure` is
    straightforward but kept abstract here so the theorem composes
    with any choice of probability framework: the input
    `h_perturbation : |ρ̂_pop − ρ_r*| ≤ δ_n` IS the deterministic
    statement on the good event, and the conclusion bounds the
    estimator error on the same event. -/

-- DELETED — Phase 3′-B, session 99.
-- Inverted-form plateau-path finite-sample wrapper superseded by
-- the Saxe-form composition of `signed_recovery_pos_magnitude_jepa`
-- with `sample_eigenvalue_perturbation`.
/-
**Theorem 3.2′ (Plateau-path finite-sample ρ-recovery, positive branch).**
Inverted-form composition.

theorem plateau_path_finite_sample_rate_pos
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d) (_hrho_pos : 0 < (eb.pairs r).rho)
    -- Sample-side plateau observable: σ̂(ε) := σ_n(T_hat(ε)).
    (sigma_at_T_hat : ℝ → ℝ)
    (rho_hat_pop : ℝ)  -- sample-side plateau height ρ̂_r* := λ̂_r* / μ̂_r
    (hrho_hat_pop_pos : 0 < rho_hat_pop)
    (K_plateau : ℝ) (hK_plateau_pos : 0 < K_plateau)
    -- Sample-side plateau hypothesis (would come from
    -- signed_recovery_pos_magnitude_plateau applied to sample dynamics).
    (h_plateau_sample : ∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma_at_T_hat ε - rho_hat_pop ^ L|
          ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
    -- Sample-eigenvalue perturbation (Layer 3.1 output).
    (delta_n : ℝ) (_hδn_pos : 0 < delta_n)
    (h_perturbation : |rho_hat_pop - (eb.pairs r).rho| ≤ delta_n) :
    ∃ (rho_estimator : ℝ → ℝ) (eps_max C_eps : ℝ),
        0 < eps_max ∧ 0 < C_eps ∧
      ∀ ε : ℝ, 0 < ε → ε < eps_max →
        |rho_estimator ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n := by
  -- Step 1: plateau → ρ̂ rate via rho_hat_plateau_rate (on sample-side ρ̂_pop).
  obtain ⟨ε_0, C_plat, hε0_pos, _hε0_lt_one, hC_plat_pos, h_rate⟩ :=
    rho_hat_plateau_rate L hL rho_hat_pop hrho_hat_pop_pos sigma_at_T_hat
      K_plateau hK_plateau_pos h_plateau_sample
  -- Step 2: define the estimator ρ̂_n(ε) := σ̂(ε)^{1/L}.
  refine ⟨fun ε => Real.rpow (sigma_at_T_hat ε) ((1 : ℝ) / L),
          ε_0, C_plat, hε0_pos, hC_plat_pos, ?_⟩
  intro ε hε_pos hε_lt
  -- Step 3: triangle inequality.
  --   |ρ̂_n(ε) − ρ_r*|  ≤  |ρ̂_n(ε) − ρ̂_pop|  +  |ρ̂_pop − ρ_r*|
  --                    ≤  C_plat · ε^{1/L} · |log ε|  +  δ_n.
  have h_plat_term := h_rate ε hε_pos hε_lt
  calc |Real.rpow (sigma_at_T_hat ε) ((1 : ℝ) / L) - (eb.pairs r).rho|
      ≤ |Real.rpow (sigma_at_T_hat ε) ((1 : ℝ) / L) - rho_hat_pop|
        + |rho_hat_pop - (eb.pairs r).rho| := abs_sub_le _ _ _
    _ ≤ C_plat * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n :=
        add_le_add h_plat_term h_perturbation
-/

/-! ## §3.3 — High-probability lift (measure-theoretic plumbing)

    Lifts the deterministic plateau-path finite-sample rate from
    "holds pointwise on a good event `G`" to "holds with probability
    ≥ `μ(G)`". Pure measure-theoretic plumbing; combines with matrix
    Bernstein (named axiom `matrix_bernstein_subgaussian` in
    `Concentration.lean`) to produce the probabilistic paper-2
    headline.

    **Composition pattern.** A typical use chains three results:
      (1) `matrix_bernstein_subgaussian` (axiom) — gives a Bernstein
          good event `G_B` with `μ(G_B) ≥ 1 − ν` on which
          `‖Σ̂ − Σ‖_F ≤ radius(n, ν)`.
      (2) `sample_eigenvalue_perturbation` (Layer 3.1, deterministic) —
          on `G_B`, gives `|ρ̂_pop − ρ_r*| ≤ C_pert · radius(n, ν)`.
      (3) `plateau_path_finite_sample_rate_pos` (Layer 3.2,
          deterministic) — on `G_B`, gives
          `|ρ̂_n(ε) − ρ_r*| ≤ C_ε · ε^{1/L}|log ε| + C_pert · radius(n,ν)`.
      (4) This theorem — lifts the pointwise rate on `G_B` to the
          probabilistic statement
          `μ{ω : rate holds} ≥ μ(G_B) ≥ 1 − ν`.
-/

-- DELETED — Phase 3′-B, session 99. Inverted-form high-prob wrapper.
/-
theorem plateau_path_finite_sample_rate_pos_high_prob
    {d : ℕ}
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ)
    (r : Fin d)
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
    (ν : ℝ) (hν_pos : 0 < ν) (hν_lt_one : ν < 1)
    -- Deterministic rate constants + sample-noise radius.
    (rho_estimator : Ω → ℝ → ℝ)
    (eps_max C_eps delta_n : ℝ)
    -- The good event: probability ≥ 1 − ν, rate holds pointwise.
    (G : Set Ω)
    (hG_prob : ((μ : MeasureTheory.Measure Ω) G).toReal ≥ 1 - ν)
    (h_rate_on_G : ∀ ω ∈ G, ∀ ε, 0 < ε → ε < eps_max →
        |rho_estimator ω ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n) :
    ((μ : MeasureTheory.Measure Ω)
        {ω | ∀ ε, 0 < ε → ε < eps_max →
              |rho_estimator ω ε - (eb.pairs r).rho|
                ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n}).toReal
      ≥ 1 - ν := by
  -- G ⊆ {ω | rate holds}, by h_rate_on_G.
  have h_subset : G ⊆ {ω | ∀ ε, 0 < ε → ε < eps_max →
      |rho_estimator ω ε - (eb.pairs r).rho|
        ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n} := by
    intro ω hω ε hε_pos hε_lt
    exact h_rate_on_G ω hω ε hε_pos hε_lt
  -- Monotonicity of the underlying measure.
  have h_mono : (μ : MeasureTheory.Measure Ω) G ≤
      (μ : MeasureTheory.Measure Ω) {ω | ∀ ε, 0 < ε → ε < eps_max →
        |rho_estimator ω ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n} :=
    MeasureTheory.measure_mono h_subset
  -- Push monotonicity through `.toReal`. The larger measure is bounded by
  -- μ(univ) = 1 (probability measure), hence finite.
  set A : Set Ω := {ω | ∀ ε, 0 < ε → ε < eps_max →
        |rho_estimator ω ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + delta_n} with hA_def
  have h_finite : (μ : MeasureTheory.Measure Ω) A ≠ ⊤ :=
    (MeasureTheory.measure_lt_top (μ : MeasureTheory.Measure Ω) A).ne
  have h_toReal := ENNReal.toReal_mono h_finite h_mono
  linarith [hG_prob]
-/

end JepaRhoRecovery
