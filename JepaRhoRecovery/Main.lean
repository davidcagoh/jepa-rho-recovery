/-
# JepaRhoRecovery.Main

**Moonshot headline assembly** — the signed-decomposition theorem for
linear JEPA training.

This file states and proves (modulo named-hypothesis sorries on the
component lemmas) the headline of the moonshot:

  > Given an estimator `ρ̂_r(ε)` produced by the layer-level construction
  > (sign-id via Layer 4.2(i), positive-magnitude inversion via 4.2(ii),
  > mixed-sign ordering via 5.1), there is a single positive threshold
  > `ε_max` below which sign identification, the magnitude rate, and the
  > ordering claim all hold simultaneously.

The proof is the genuine **uniform-`ε_max` finite-`Finset` reduction**:
each per-feature existential `ε₀(r) > 0` (from the layer-level
hypotheses) is collapsed to a single `ε_max > 0` via
`finset_forall_eps₂`.

## CompCert convention

Per the spinoff's vacuity discipline, each hypothesis below is a
non-trivially-constraining bundle of one layer's output:

  * `h_sign_pos` / `h_sign_neg` / `h_sign_zero` — Layer 4.2(i) trichotomy
    forwards (`SignedRecovery.sign_identification_pos_forward` and
    siblings; sorry-free).
  * `h_pos_mag` — Layer 4.2(ii) magnitude rate
    (`SignedRecovery.signed_recovery_pos_magnitude_jepa`; sorry-free
    modulo the Path C envelope-sharpening named sorry
    `CriticalTime.purified_laurent_bound`).
  * `h_neg_mag` — Layer 4.2(ii⁻) negative-branch magnitude rate
    (`SignedRecovery.signed_recovery_neg_magnitude_jepa`; sorry-free
    composition of the trajectory-derived λ̂-rate
    `signed_recovery_neg_lambda_rate` with an ordinary sample-covariance
    concentration bound on μ̂, taken as a hypothesis the same way
    `h_pos_mag`'s constant is; combined via the delta method
    `ρ̂ = λ̂/μ̂`). Unlike `h_pos_mag`, the bound carries an additive
    `C · delta_mu r` floor that does not vanish as `ε → 0` — the
    irreducible sample-noise term, honestly reflecting that magnitude
    recovery on the negative branch is not obstructed but requires
    the covariance input (§4.2(iii) revisited).
  * `h_ordering` — Layer 5.1 (`MixedOrdering.mixed_sign_ordering`;
    sorry-free).

Each hypothesis is therefore the publicly-stated output of a separate
layer file; this file does not duplicate their content but bundles
them under a common threshold. The "honesty" of the headline is
therefore inherited from the layer files.
-/

import JepaRhoRecovery.Basic
import JepaRhoRecovery.QuasiStatic
import JepaRhoRecovery.DiagonalODE
import JepaRhoRecovery.Inversion
import JepaRhoRecovery.SignedODE
import JepaRhoRecovery.SignedRecovery
import JepaRhoRecovery.PlateauEstimator
import JepaRhoRecovery.MixedOrdering
import JepaRhoRecovery.SampleNoise
import JepaRhoRecovery.FiniteSample

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## Headline — signed decomposition theorem

The signed-decomposition theorem says: under a partition `(P, N)` of the
spectrum into positive/negative ρ_r* indices and a gap condition, the
JEPA training trajectory admits an estimator ρ̂ that

  (1) recovers the sign of each ρ_r* (for r ∈ P ∪ N) and is zero on
      the ker-spectrum (ρ_r* = 0);
  (2) achieves the inversion rate `O(ε^{1/L}|log ε|)` for r ∈ P;
  (3) achieves the composed rate `O(ε^{1/L}|log ε| + delta_mu r)` for
      r ∈ N (Fix 1 — `h_neg_mag`, composing the trajectory-derived
      λ̂-rate with a μ̂-concentration bound via the delta method; the
      additive `delta_mu r` term is the irreducible sample-noise floor,
      not a trajectory-only rate — see `SignedRecovery.
      signed_recovery_neg_magnitude_jepa`);
  (4) under the gap condition, positive learning critical times are
      strictly less than negative suppression thresholds.

The Lean statement bundles the five layer outputs as named hypotheses
and asserts the uniform-`ε_max` existential.
-/

/-- **Theorem (Signed decomposition of the regression structure via linear
    JEPA training — moonshot headline).**

    Given the layer-level outputs (each a non-trivially-constraining
    hypothesis), there is a single positive threshold `ε_max` and rate
    constant `C_eps` such that, for every `ε ∈ (0, ε_max)`, the
    estimator `ρ̂` exhibits:

      (1) `sign(ρ̂ r) = sign(ρ_r*)` for every `r ∈ P ∪ N`, and `ρ̂ r = 0`
          on `ker (sign ρ*)`;
      (2) `|ρ̂ r − ρ_r*| ≤ C_eps · ε^{1/L} · |log ε|` for `r ∈ P`;
      (3) `|ρ̂ r − ρ_r*| ≤ C_eps · ε^{1/L} · |log ε| + C_eps · delta_mu r`
          for `r ∈ N` (Fix 1: negative-branch magnitude, bundled from
          `h_neg_mag` — no longer the pure sign-only obstruction of the
          original Layer 4.2(iii) statement; the additive term is the
          sample-noise floor from the μ̂-concentration input);
      (4) under the gap condition `min_{s ∈ P} ρ_s* > max_{r ∈ N} |ρ_r*|`,
          `τ_pos(s, ε) < τ_neg(r, ε)` for every `s ∈ P, r ∈ N`.

    **Proof sketch.** Each layer hypothesis gives a per-feature `ε_0(r)`.
    Apply `finset_forall_eps₂` over `P` (resp. `N`) to extract a uniform
    threshold `ε_pos_min`/`ε_pos_mag` (resp. `ε_neg_min`/`ε_neg_mag`) for
    sign and magnitude; intersect with `ε_ord` from `h_ordering`. The
    resulting `ε_max := min(ε_pos_min, ε_neg_min, ε_pos_mag, ε_neg_mag,
    ε_ord, 1)` is positive. `C_eps` is taken as the maximum of the
    per-feature `C(r)` from `h_pos_mag` **and** `h_neg_mag` pooled over
    `P ∪ N` (sum over a finite `Finset`, defaulting to `1` if empty). The
    proof then case-splits on `ε < ε_max` and dispatches each conjunct
    from the corresponding layer output.
-/
theorem signed_decomposition
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (_hL : 2 ≤ L)
    -- Partition of the spectrum.
    (P N : Finset (Fin d))
    (_hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
    (_hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
    (hPN_disjoint : Disjoint P N)
    (_hGap : ∀ s ∈ P, ∀ r ∈ N, |(eb.pairs r).rho| < (eb.pairs s).rho)
    -- Per-feature estimator (layer-level construction; see
    -- `SignedRecovery.signed_recovery_pos_magnitude_jepa`).
    (rho_hat : Fin d → ℝ → ℝ)
    -- (1) Sign identification — Layer 4.2(i) trichotomy forwards.
    (h_sign_pos : ∀ r ∈ P, ∃ ε_0 : ℝ, 0 < ε_0 ∧
        ∀ ε, 0 < ε → ε < ε_0 → 0 < rho_hat r ε)
    (h_sign_neg : ∀ r ∈ N, ∃ ε_0 : ℝ, 0 < ε_0 ∧
        ∀ ε, 0 < ε → ε < ε_0 → rho_hat r ε < 0)
    (h_sign_zero : ∀ r : Fin d, (eb.pairs r).rho = 0 →
        ∀ ε, 0 < ε → ε < 1 → rho_hat r ε = 0)
    -- (2) Positive-magnitude recovery rate — Layer 4.2(ii).
    (h_pos_mag : ∀ r ∈ P, ∃ ε_0 C : ℝ, 0 < ε_0 ∧ 0 < C ∧
        ∀ ε, 0 < ε → ε < ε_0 →
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
    -- (3) Negative-magnitude recovery rate — Layer 4.2(ii⁻), Fix 1.
    -- `delta_mu r` is the μ̂-concentration radius for feature `r`
    -- (sample-noise floor; see `SignedRecovery.
    -- signed_recovery_neg_magnitude_jepa`), non-vanishing as ε → 0.
    (delta_mu : Fin d → ℝ) (hδmu_nonneg : ∀ r ∈ N, 0 ≤ delta_mu r)
    (h_neg_mag : ∀ r ∈ N, ∃ ε_0 C : ℝ, 0 < ε_0 ∧ 0 < C ∧
        ∀ ε, 0 < ε → ε < ε_0 →
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C * delta_mu r)
    -- (4) Mixed-sign ordering — Layer 5.1.
    (tau_pos tau_neg : Fin d → ℝ → ℝ)
    (h_ordering : ∃ eps_max : ℝ, 0 < eps_max ∧
        ∀ ε, 0 < ε → ε < eps_max →
          ∀ s ∈ P, ∀ r ∈ N, tau_pos s ε < tau_neg r ε) :
    -- Conclusion: uniform `ε_max` under which all properties hold.
    ∃ eps_max C_eps : ℝ, 0 < eps_max ∧ 0 < C_eps ∧
      ∀ ε, 0 < ε → ε < eps_max →
        -- (1) Sign.
        (∀ r ∈ P, 0 < rho_hat r ε) ∧
        (∀ r ∈ N, rho_hat r ε < 0) ∧
        (∀ r : Fin d, (eb.pairs r).rho = 0 → rho_hat r ε = 0) ∧
        -- (2) Positive magnitude.
        (∀ r ∈ P, |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε|) ∧
        -- (3) Negative magnitude (Fix 1) — composed rate with the
        --     sample-noise floor `C_eps · delta_mu r`.
        (∀ r ∈ N, |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_mu r) ∧
        -- (4) Ordering.
        (∀ s ∈ P, ∀ r ∈ N, tau_pos s ε < tau_neg r ε) := by
  classical
  -- Step 1: pre-pick per-feature constants C(r) > 0 from `h_pos_mag`
  -- (for r ∈ P) and `h_neg_mag` (for r ∈ N), and define a uniform
  -- C_eps as their pooled sum + 1 (positive, dominates each branch).
  let C_per : Fin d → ℝ :=
    fun r => if hr : r ∈ P then (h_pos_mag r hr).choose_spec.choose
      else if hr' : r ∈ N then (h_neg_mag r hr').choose_spec.choose
      else 0
  have hC_per_nonneg : ∀ r : Fin d, 0 ≤ C_per r := by
    intro r
    by_cases hr : r ∈ P
    · simp only [C_per, dif_pos hr]
      exact (h_pos_mag r hr).choose_spec.choose_spec.2.1.le
    · by_cases hr' : r ∈ N
      · simp only [C_per, dif_neg hr, dif_pos hr']
        exact (h_neg_mag r hr').choose_spec.choose_spec.2.1.le
      · simp [C_per, dif_neg hr, dif_neg hr']
  -- Step 2: uniform-(ε_max, C_eps) bound, pooled over P ∪ N.
  -- Use the dominating constant `C_eps`, which weakens each per-r bound
  -- monotonically and lets a single `finset_forall_eps₂` reduction close
  -- the existential.
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
  obtain ⟨ε_pos_mag, hε_pos_mag_pos, h_pos_mag_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ P,
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ P ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε =>
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε|)
        (fun r hr _ _ => by
          refine ⟨(h_pos_mag r hr).choose, ?_, ?_⟩
          · exact (h_pos_mag r hr).choose_spec.choose_spec.1
          · intro ε hε_pos hε_lt
            -- Per-r bound with C(r): use hbound from h_pos_mag, then
            -- monotonicity in C: C(r) ≤ C_eps and rest is nonneg.
            have hC_r_bound :=
              (h_pos_mag r hr).choose_spec.choose_spec.2.2 ε hε_pos hε_lt
            have hC_r_eq : (h_pos_mag r hr).choose_spec.choose = C_per r := by
              simp [C_per, dif_pos hr]
            rw [hC_r_eq] at hC_r_bound
            have hC_r_le : C_per r ≤ C_eps := hC_per_dominates_P r hr
            have h_rpow_nn : 0 ≤ ε ^ ((1 : ℝ) / L) := Real.rpow_nonneg hε_pos.le _
            have h_log_nn : 0 ≤ |Real.log ε| := abs_nonneg _
            have h_factor_nn : 0 ≤ ε ^ ((1 : ℝ) / L) * |Real.log ε| :=
              mul_nonneg h_rpow_nn h_log_nn
            calc |rho_hat r ε - (eb.pairs r).rho|
                ≤ C_per r * ε ^ ((1 : ℝ) / L) * |Real.log ε| := hC_r_bound
              _ = C_per r * (ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by ring
              _ ≤ C_eps * (ε ^ ((1 : ℝ) / L) * |Real.log ε|) :=
                  mul_le_mul_of_nonneg_right hC_r_le h_factor_nn
              _ = C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by ring)
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  -- Step 2′: uniform-(ε_max, C_eps) bound for negative magnitude (Fix 1).
  obtain ⟨ε_neg_mag, hε_neg_mag_pos, h_neg_mag_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ N,
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_mu r := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ N ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε =>
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_mu r)
        (fun r hr _ _ => by
          have hrnP : r ∉ P := fun hrP => absurd hr (Finset.disjoint_left.mp hPN_disjoint hrP)
          refine ⟨(h_neg_mag r hr).choose, ?_, ?_⟩
          · exact (h_neg_mag r hr).choose_spec.choose_spec.1
          · intro ε hε_pos hε_lt
            have hC_r_bound :=
              (h_neg_mag r hr).choose_spec.choose_spec.2.2 ε hε_pos hε_lt
            have hC_r_eq : (h_neg_mag r hr).choose_spec.choose = C_per r := by
              simp only [C_per, dif_neg hrnP, dif_pos hr]
            rw [hC_r_eq] at hC_r_bound
            have hC_r_le : C_per r ≤ C_eps := hC_per_dominates_N r hr
            have h_rpow_nn : 0 ≤ ε ^ ((1 : ℝ) / L) := Real.rpow_nonneg hε_pos.le _
            have h_log_nn : 0 ≤ |Real.log ε| := abs_nonneg _
            have h_factor_nn : 0 ≤ ε ^ ((1 : ℝ) / L) * |Real.log ε| :=
              mul_nonneg h_rpow_nn h_log_nn
            have hδ_nn : 0 ≤ delta_mu r := hδmu_nonneg r hr
            calc |rho_hat r ε - (eb.pairs r).rho|
                ≤ C_per r * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_per r * delta_mu r := hC_r_bound
              _ ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_eps * delta_mu r := by
                  have h1 := mul_le_mul_of_nonneg_right hC_r_le h_factor_nn
                  have h2 := mul_le_mul_of_nonneg_right hC_r_le hδ_nn
                  nlinarith [h1, h2])
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  -- Step 3: uniform threshold for sign-positivity.
  obtain ⟨ε_sign_pos, hε_sign_pos_pos, h_sign_pos_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ P, 0 < rho_hat r ε := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ P ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε => 0 < rho_hat r ε)
        (fun r hr _ _ => h_sign_pos r hr)
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  -- Step 4: uniform threshold for sign-negativity.
  obtain ⟨ε_sign_neg, hε_sign_neg_pos, h_sign_neg_unif⟩ :
      ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ ε, 0 < ε → ε < ε_max → ∀ r ∈ N, rho_hat r ε < 0 := by
    obtain ⟨εm, hεm_pos, hεm⟩ :=
      finset_forall_eps₂ N ({(0 : ℕ)} : Finset ℕ)
        (fun r _ ε => rho_hat r ε < 0)
        (fun r hr _ _ => h_sign_neg r hr)
    refine ⟨εm, hεm_pos, fun ε hε₁ hε₂ r hr => hεm ε hε₁ hε₂ r hr 0 (by simp)⟩
  -- Step 5: extract ordering threshold.
  obtain ⟨ε_ord, hε_ord_pos, h_ord_unif⟩ := h_ordering
  -- Step 6: assemble. ε_max := min(everything, 1), now over six leaves
  -- (sign-pos, sign-neg, pos-mag, neg-mag, ordering, 1).
  refine ⟨min (min (min ε_sign_pos ε_sign_neg) (min ε_pos_mag ε_neg_mag))
              (min ε_ord 1),
          C_eps,
          lt_min (lt_min (lt_min hε_sign_pos_pos hε_sign_neg_pos)
                          (lt_min hε_pos_mag_pos hε_neg_mag_pos))
                  (lt_min hε_ord_pos zero_lt_one),
          hC_eps_pos, ?_⟩
  intro ε hε_pos hε_lt
  have hεA : ε < min (min ε_sign_pos ε_sign_neg) (min ε_pos_mag ε_neg_mag) :=
    lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hεB : ε < min ε_ord 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hε_lt_sign_pos : ε < ε_sign_pos :=
    lt_of_lt_of_le (lt_of_lt_of_le hεA (min_le_left _ _)) (min_le_left _ _)
  have hε_lt_sign_neg : ε < ε_sign_neg :=
    lt_of_lt_of_le (lt_of_lt_of_le hεA (min_le_left _ _)) (min_le_right _ _)
  have hε_lt_pos_mag : ε < ε_pos_mag :=
    lt_of_lt_of_le (lt_of_lt_of_le hεA (min_le_right _ _)) (min_le_left _ _)
  have hε_lt_neg_mag : ε < ε_neg_mag :=
    lt_of_lt_of_le (lt_of_lt_of_le hεA (min_le_right _ _)) (min_le_right _ _)
  have hε_lt_ord : ε < ε_ord := lt_of_lt_of_le hεB (min_le_left _ _)
  have hε_lt_one : ε < 1 := lt_of_lt_of_le hεB (min_le_right _ _)
  exact ⟨h_sign_pos_unif ε hε_pos hε_lt_sign_pos,
         h_sign_neg_unif ε hε_pos hε_lt_sign_neg,
         fun r hrho_zero => h_sign_zero r hrho_zero ε hε_pos hε_lt_one,
         h_pos_mag_unif ε hε_pos hε_lt_pos_mag,
         h_neg_mag_unif ε hε_pos hε_lt_neg_mag,
         h_ord_unif ε hε_pos hε_lt_ord⟩

/-! ## Paper-2 headline — plateau-path positive-branch recovery

    The trajectory-only ρ-recovery result. Given a positive-branch
    Bernoulli ODE trajectory bundle `σ ε t`, the plateau-derived
    estimator `ρ̂(ε) := σ(T(ε))^{1/L}` recovers `ρ = λ/μ` at rate
    `ε^{1/L}|log ε|`.

    This is the moonshot headline in its purest form: no covariance
    input, no JEPA-window hypothesis bundle, no Path-C envelope axiom.
    Composes `signed_recovery_pos_magnitude_plateau` (trajectory →
    plateau bound; session 88) with `rho_hat_plateau_rate` (plateau
    bound → ρ̂ rate; session 87) into a single statement.
-/

-- DELETED — Phase 3′-B, session 99.
-- Inverted-form `plateau_path_recovery_pos` superseded by the Saxe
-- composition realised inline in `SignedRecovery.signed_recovery_pos_magnitude_jepa`.
/-
theorem plateau_path_recovery_pos
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_below : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t →
        sigma ε t < (lambda / mu) ^ L)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 ≤ ε) :
    ∃ (T : ℝ → ℝ) (ε_0 C : ℝ),
      0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
      (∀ ε : ℝ, 0 < ε → ε < ε_0 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < ε_0 →
          0 < Real.rpow (sigma ε (T ε)) ((1 : ℝ) / L)) ∧
      (∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |Real.rpow (sigma ε (T ε)) ((1 : ℝ) / L) - lambda / mu|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
  -- Step 1: get T, K_plat from the plateau bridge.
  obtain ⟨T, K_plat, hK_pos, hT_pos, h_plat⟩ :=
    signed_recovery_pos_magnitude_plateau L hL lambda mu hlambda_pos hmu_pos
      sigma hSigma_pos hSigma_below hSigma_cont hSigma_ode hSigma_init
  -- Step 2: feed into rho_hat_plateau_rate via ρ := λ/μ.
  set ρ : ℝ := lambda / mu with hρ_def
  have hρ_pos : 0 < ρ := div_pos hlambda_pos hmu_pos
  have h_plat_ρ : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |sigma ε (T ε) - ρ ^ L| ≤ K_plat * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
    intro ε hε hε1
    have := h_plat ε hε hε1
    simpa [hρ_def] using this
  obtain ⟨ε_0, C, hε0_pos, hε0_lt1, hC_pos, h_rate⟩ :=
    rho_hat_plateau_rate L hL ρ hρ_pos (fun ε => sigma ε (T ε))
      K_plat hK_pos h_plat_ρ
  -- Step 3: assemble. T positive, rpow positive (since σ > 0), rate via h_rate.
  refine ⟨T, ε_0, C, hε0_pos, hε0_lt1, hC_pos, ?_, ?_, ?_⟩
  · intro ε hε hε_lt
    exact hT_pos ε hε (hε_lt.trans hε0_lt1)
  · intro ε hε hε_lt
    have hε1 : ε < 1 := hε_lt.trans hε0_lt1
    have hT_ε_pos : 0 < T ε := hT_pos ε hε hε1
    have hσ_pos : 0 < sigma ε (T ε) := hSigma_pos ε hε hε1 (T ε) hT_ε_pos.le
    exact Real.rpow_pos_of_pos hσ_pos _
  · exact h_rate
-/

end JepaRhoRecovery
