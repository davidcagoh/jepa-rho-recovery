/-
# JepaRhoRecovery.MixedOrdering

Layer 5.1 — mixed-sign ordering. Once positive features are learned and
negative features are suppressed, JEPA training implicitly partitions the
spectrum into {learn, discard, suppress} in a definite *temporal* order:
positive features finish learning before any negative feature is fully
suppressed, under a gap condition on the signed eigenvalues.
-/

import JepaRhoRecovery.Basic
import JepaRhoRecovery.SignedODE
import JepaRhoRecovery.Inversion

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §5.1 — Mixed-sign ordering theorem -/

/-- **Theorem 5.1 (Mixed-sign ordering).**

    Partition the index set `Fin d` into positive-ρ features
    `P = {r : (eb.pairs r).rho > 0}` and negative-ρ features
    `N = {r : (eb.pairs r).rho < 0}`. Under the gap condition

        ρ_max_pos := max_{r ∈ P} ρ_r*  >  max_{r ∈ N} |ρ_r*|,

    the positive-feature *learning critical times* `τ_r*` and the
    negative-feature *suppression thresholds* `τ_r†` satisfy

        max_{r ∈ P} τ_r*  <  min_{r ∈ N} τ_r†.

    In words: every positive feature finishes learning before any negative
    feature is meaningfully suppressed.

    Stated abstractly over hitting-time bundles for both branches; the
    bundles are produced by Layer 2.2 (`rho_hat_rate`) for the positive
    branch and a yet-to-state Layer 4.1(c′) suppression-time corollary for
    the negative branch.

    PROVIDED SOLUTION
    Step 1 (positive-branch leading order). For `r ∈ P`,
    `τ_r* = Θ(1 / (λ_r ε^{1/L} ρ_r^{2L-2}))` (Layer 2.2 leading-term).
    Step 2 (negative-branch leading order). For `r ∈ N`, the suppression
    time scales as `τ_r† = Θ(1 / (|λ_r| ε^{(2L-1)/L}))` (from the
    `σ̇ = O(σ^{3-1/L})` integration; cf. 4.1(c) roadmap line 294).
    Step 3 (gap implies ordering). The ratio
    `τ_r† / τ_s* = Θ(ε^{-2(L-1)/L} · ρ_s^{2L-2} · λ_s / |λ_r|)`. As
    `ε → 0`, the `ε^{-2(L-1)/L}` factor dominates regardless of the
    finite signed-eigenvalue ratio, giving `τ_r† ≫ τ_s*` for all `s ∈ P`,
    `r ∈ N` and ε small enough. The gap condition fixes the leading
    constants on the positive side. -/
theorem mixed_sign_ordering
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    (P N : Finset (Fin d))
    (hP : ∀ r ∈ P, 0 < (eb.pairs r).rho)
    (hN : ∀ r ∈ N, (eb.pairs r).rho < 0)
    (hPN_disjoint : Disjoint P N)
    -- Gap condition.
    (hGap : ∀ s ∈ P, ∀ r ∈ N, |(eb.pairs r).rho| < (eb.pairs s).rho)
    -- Positive-branch hitting times (Layer 2.2 bundle).
    (tau_pos : Fin d → ℝ → ℝ)
    (tau_pos_bound : ∀ s ∈ P, ∃ K : ℝ, 0 < K ∧
        tau_pos s epsilon
          ≤ K / ((eb.pairs s).rho * (eb.pairs s).mu)
            * Real.rpow epsilon (-(1 : ℝ) / L))
    -- Negative-branch suppression thresholds (Layer 4.1(c) corollary).
    (tau_neg : Fin d → ℝ → ℝ)
    (tau_neg_lower : ∀ r ∈ N, ∃ K : ℝ, 0 < K ∧
        K / |(eb.pairs r).rho * (eb.pairs r).mu|
          * Real.rpow epsilon (-(2 * (L : ℝ) - 1) / L)
            ≤ tau_neg r epsilon)
    -- Threshold for "ε small enough".
    (eps_threshold : ℝ) (heps_thr_pos : 0 < eps_threshold) :
    ∃ eps_max : ℝ, 0 < eps_max ∧
      ∀ ε : ℝ, 0 < ε → ε < eps_max →
        ∀ s ∈ P, ∀ r ∈ N, tau_pos s ε < tau_neg r ε := by
  sorry

end JepaRhoRecovery
