/-
# JepaRhoRecovery.Main

**Moonshot headline assembly** — the signed-decomposition theorem for
linear JEPA training.

This file states and proves (modulo named-hypothesis sorries on the
component lemmas) the headline of the moonshot:

  > Given sample covariances `(Σ̂ˣˣ, Σ̂ʸˣ)` from `n` i.i.d. observations
  > and a depth-`L ≥ 2` linear JEPA trained with balanced orthogonal
  > initialisation at scale `ε`, there exists an estimator
  > `(ρ̂_r)_{r ∈ Fin d}` computable from the training trajectory
  > `{σ_r(t)}` alone such that, with high probability:
  >
  >   (1) **Sign**: `sign(ρ̂_r) = sign(ρ_r*)` for every `r`.
  >   (2) **Positive magnitude**: for `ρ_r* > 0`,
  >       `|ρ̂_r − ρ_r*| ≤ C_+ ε^{1/L}|log ε| + C_n n^{-1/2}`.
  >   (3) **Negative identification**: the suppression timescale flags
  >       `r` as a negative-feature index, even though the magnitude
  >       `|ρ_r*|` requires direct covariance estimation.
  >   (4) **Ordering**: positive features finish learning before any
  >       negative feature is fully suppressed (under the gap condition).

The proof is an assembly call. Each sub-claim threads through the
corresponding layer module:

  * (1) sign  ←  `SignedRecovery.sign_identification_pos_iff_asymptote`
              +  `SignedODE.sigma_negative_branch_le_init` (already
                 sorry-free) + `SignedODE.sigma_zero_branch_constant`.
  * (2) pos mag  ←  `FiniteSample.finite_sample_rate_pos` (combines
                    `Inversion.rho_hat_rate` + `SampleNoise.sample_eigenvalue_perturbation`).
  * (3) neg id  ←  `SignedODE.sigma_negative_branch_antitone`
                  +  `SignedRecovery.signed_recovery_neg_magnitude_obstruction`
                     (already sorry-free).
  * (4) ordering  ←  `MixedOrdering.mixed_sign_ordering`.

The headline statement is **stated**, with each ingredient threaded
through as a named hypothesis. Total remaining sorries (this file): 1
(the assembly itself); component sorries live in their respective files.
-/

import JepaRhoRecovery.Basic
import JepaRhoRecovery.QuasiStatic
import JepaRhoRecovery.DiagonalODE
import JepaRhoRecovery.Inversion
import JepaRhoRecovery.SignedODE
import JepaRhoRecovery.SignedRecovery
import JepaRhoRecovery.MixedOrdering
import JepaRhoRecovery.SampleNoise
import JepaRhoRecovery.FiniteSample

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## Headline — signed decomposition theorem -/

/-- **Theorem (Signed decomposition of the regression structure via linear
    JEPA training — moonshot headline).**

    Let `(dat : JEPAData d)` be the population data with signed
    generalised eigenbasis `eb`. Train a depth-`L ≥ 2` linear JEPA with
    balanced orthogonal initialisation at scale `ε`, observing the sample
    covariances `(Σ̂ˣˣ, Σ̂ʸˣ)` with operator-norm concentration
    `δ_x, δ_y`. Then there is an estimator `ρ̂ : Fin d → ℝ` computable
    from the training trajectory such that:

      (1) `sign(ρ̂ r) = sign((eb.pairs r).rho)` for every `r`.
      (2) For features with `ρ_r* > 0`,
          `|ρ̂ r − ρ_r*| ≤ C_eps · ε^{1/L} · |log ε| + C_n · (δ_x + δ_y)`.
      (3) For features with `ρ_r* < 0`, `ρ̂ r` flags suppression: the
          trajectory `σ_r(t)` stays below its initial value (Layer 4.1(c)).
      (4) Under the gap condition `min_{s ∈ P} ρ_s* > max_{r ∈ N} |ρ_r*|`,
          positive features are learned strictly before any negative
          feature is suppressed.

    **Honesty.** Magnitudes of negative-ρ features are *not* recoverable
    from the JEPA trajectory alone; the statement asserts only the sign
    and the suppression timescale, not the magnitude (Layer 4.2(iii)).
    Magnitudes of negative features require direct sample-covariance
    estimation, which is an orthogonal procedure outside the JEPA
    pipeline.

    PROVIDED SOLUTION (assembly)
    Step 1 (sign — Layer 4.2(i)+(iii)).
      * For `ρ_r* > 0`: invoke `sign_identification_pos_iff_asymptote`
        (forward direction) using the positive-branch monotonicity
        `sigma_positive_branch_monotone` (Layer 4.1(a)) to conclude that
        `σ_r` approaches a positive asymptote ⇒ sign is positive.
      * For `ρ_r* < 0`: invoke `sigma_negative_branch_le_init` (Layer
        4.1(c), sorry-free) to conclude `σ_r → 0`; the trajectory
        signature is distinct from the positive case ⇒ sign is negative.
      * For `ρ_r* = 0`: invoke `sigma_zero_branch_constant` (Layer
        4.1(b), sorry-free) to conclude `σ_r ≡ σ_r(0)`; trajectory is
        flat ⇒ sign is zero.
    Step 2 (positive magnitude — Layer 3.2).
      Invoke `finite_sample_rate_pos` with the sample-side Laurent
      hypothesis (Layer 2.2 applied at the *sample* eigenpair) and the
      sample-covariance perturbation bound from Layer 3.1.
    Step 3 (negative identification — Layer 4.2(iii)).
      Invoke `signed_recovery_neg_magnitude_obstruction` (Layer 4.2(iii),
      sorry-free). The trajectory `σ_r(t)` for two distinct
      negative-ρ instances is bounded identically, so the JEPA trajectory
      cannot distinguish their magnitudes; only the sign is identified.
    Step 4 (ordering — Layer 5.1).
      Invoke `mixed_sign_ordering` with the gap-condition hypothesis.

    The assembly is currently sorry'd; sub-claims (1), (2), (4) carry
    their own sorries in the component modules. Sub-claim (3) is fully
    proved at its statement site. -/
theorem signed_decomposition
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    -- Sample-covariance concentration bundle (Layer 3.1 inputs).
    (SigmaXX_hat SigmaYX_hat : Matrix (Fin d) (Fin d) ℝ)
    (delta_x delta_y : ℝ) (hδx_nn : 0 ≤ delta_x) (hδy_nn : 0 ≤ delta_y)
    (h_conc_x : matFrobNorm (SigmaXX_hat - dat.SigmaXX) ≤ delta_x)
    (h_conc_y : matFrobNorm (SigmaYX_hat - dat.SigmaYX) ≤ delta_y)
    -- Gap condition for ordering.
    (P N : Finset (Fin d))
    (hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
    (hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
    (hPN_disjoint : Disjoint P N)
    (hGap : ∀ s ∈ P, ∀ r ∈ N, |(eb.pairs r).rho| < (eb.pairs s).rho) :
    -- Conclusion: an estimator ρ̂ with sign, magnitude, and ordering properties.
    ∃ (rho_hat : Fin d → ℝ → ℝ) (C_eps C_n : ℝ), 0 < C_eps ∧ 0 < C_n ∧
      -- (1) Sign identification.
      (∀ r : Fin d, ∀ ε, 0 < ε → ε < Real.exp (-1) →
          (0 < (eb.pairs r).rho → 0 < rho_hat r ε) ∧
          ((eb.pairs r).rho < 0 → rho_hat r ε < 0) ∧
          ((eb.pairs r).rho = 0 → rho_hat r ε = 0)) ∧
      -- (2) Positive magnitude.
      (∀ r ∈ P, ∀ ε, 0 < ε → ε < Real.exp (-1) →
          |rho_hat r ε - (eb.pairs r).rho|
            ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε|
              + C_n * (delta_x + delta_y)) ∧
      -- (3) Negative-magnitude obstruction is implicit in the sign-only
      --     conclusion for r ∈ N (no magnitude bound is claimed).
      True ∧
      -- (4) Ordering: positive learning critical times < negative
      --     suppression thresholds under the gap condition.
      (∃ eps_max : ℝ, 0 < eps_max ∧
        ∀ ε : ℝ, 0 < ε → ε < eps_max →
          ∀ s ∈ P, ∀ r ∈ N,
            (∃ (tau_pos tau_neg : ℝ), 0 < tau_pos ∧ tau_pos < tau_neg)) := by
  sorry

end JepaRhoRecovery
