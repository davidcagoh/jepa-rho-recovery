/-
# JepaRhoRecovery.SampleNoise

Layer 3.1 — perturbation of generalised eigenstructure under sample
covariance noise. Population covariances `Σˣˣ`, `Σʸˣ` are replaced by
sample estimates `Σ̂ˣˣ`, `Σ̂ʸˣ` from `n` i.i.d. observations; the
generalised eigenpairs `(v_r*, ρ_r*)` of the population problem and
`(v̂_r, ρ̂_r)` of the sample problem are related by perturbation theory.

This file states the perturbation bound *abstractly*: the
operator-norm concentration `‖Σ̂ − Σ‖_op ≤ δ(n)` is taken as a hypothesis
(produced by standard sub-Gaussian / sub-exponential concentration —
out of scope for Mathlib's current generalised-eigenvalue API). The
output is a perturbation bound on `(v̂_r, ρ̂_r)` matching paper §3 of the
roadmap.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §3.1 — Perturbation bound for generalised eigenvalues -/

/-- **Theorem 3.1 (Sample-covariance perturbation of ρ_r*).**

    Restated (v2, session 78 — vacuity fix). Previous form
    `∃ rho_hat, ∀ r, |rho_hat r − ρ_r*| ≤ C·δ` was trivially satisfied by
    `rho_hat := (eb.pairs ·).rho` (Aristotle `e71b355e` produced exactly
    that degenerate witness). Fix: take `rho_hat` as an **input** bound to
    the sample matrices via the generalised eigenproblem hypothesis
    `h_sample_eigen`; conclude per-sample-eigenvalue closeness to *some*
    population eigenvalue (Weyl).

    Given sample matrices `(Σ̂ˣˣ, Σ̂ʸˣ)` with operator-norm concentration
    `‖Σ̂ˣˣ − Σˣˣ‖_F ≤ δ_x`, `‖Σ̂ʸˣ − Σʸˣ‖_F ≤ δ_y`, and a candidate
    generalised eigenpair `(rho_hat r, v_hat r)` of the SAMPLE pair
    (i.e. `Σ̂ʸˣ v̂_r = ρ̂_r · Σ̂ˣˣ v̂_r` with `v̂_r ≠ 0`), there exists a
    `dat`-dependent constant `C > 0` such that each sample eigenvalue
    `ρ̂_r` lies within `C · (δ_x + δ_y)` of some population eigenvalue.

    PROVIDED SOLUTION (3 steps; see request `11_sample_eigenvalue_perturbation_v2.md`)
    Step 1. Reduce both pairs to symmetric eigenproblems via
    `w = (Σˣˣ)^{1/2} v`. Define `M = (Σˣˣ)^{-1/2} Σʸˣ (Σˣˣ)^{-1/2}` and
    `M̂ = (Σ̂ˣˣ)^{-1/2} Σ̂ʸˣ (Σ̂ˣˣ)^{-1/2}`.
    Step 2. Bound `‖M̂ − M‖_op` by `O(‖Σˣˣ⁻¹‖² · (‖Σʸˣ‖_op · δ_x + δ_y))`
    via product-rule expansion on matrix square-root / inverse.
    Step 3. Apply Weyl: each eigenvalue of `M̂` is within `‖M̂ − M‖_op`
    of some eigenvalue of `M`. Combine with `h_sample_eigen` to translate
    back to the generalised problem.

    Set `C := O(‖Σˣˣ⁻¹‖² · (‖Σʸˣ‖_op + 1))`.
-/
theorem sample_eigenvalue_perturbation
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (SigmaXX_hat SigmaYX_hat : Matrix (Fin d) (Fin d) ℝ)
    (delta_x delta_y : ℝ) (hδx_nn : 0 ≤ delta_x) (hδy_nn : 0 ≤ delta_y)
    -- Frobenius-norm concentration (taken as hypothesis; produced by
    -- sub-Gaussian / sub-exponential matrix Bernstein, out of scope here).
    (h_conc_x : matFrobNorm (SigmaXX_hat - dat.SigmaXX) ≤ delta_x)
    (h_conc_y : matFrobNorm (SigmaYX_hat - dat.SigmaYX) ≤ delta_y)
    -- Sample generalised eigenpair: supplied externally, MUST satisfy the
    -- generalised eigenproblem against the SAMPLE covariances. This is the
    -- vacuity fix: `rho_hat := population` is no longer admissible because
    -- `h_sample_eigen` would then constrain `Σ̂ʸˣ v = ρ_r* Σ̂ˣˣ v`, which
    -- is false unless `Σ̂ = Σ`.
    (rho_hat : Fin d → ℝ)
    (v_hat   : Fin d → EuclideanSpace ℝ (Fin d))
    (h_v_hat_nonzero  : ∀ r, v_hat r ≠ 0)
    (h_sample_eigen   : ∀ r,
        SigmaYX_hat *ᵥ v_hat r = (rho_hat r) • (SigmaXX_hat *ᵥ v_hat r)) :
    -- Per-sample-eigenvalue Weyl closeness to SOME population eigenvalue.
    ∃ C : ℝ, 0 < C ∧
      ∀ r : Fin d, ∃ s : Fin d,
        |rho_hat r - (eb.pairs s).rho| ≤ C * (delta_x + delta_y) := by
  sorry

end JepaRhoRecovery
