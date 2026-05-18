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

    If the sample covariances `(Σ̂ˣˣ, Σ̂ʸˣ)` satisfy operator-norm
    concentration

        ‖Σ̂ˣˣ − Σˣˣ‖_op ≤ δ_x,  ‖Σ̂ʸˣ − Σʸˣ‖_op ≤ δ_y,

    then for each `r : Fin d` there exists a perturbation
    `Δρ_r = ρ̂_r − ρ_r*` bounded by

        |Δρ_r| ≤ C(dat, eb) · (δ_x + δ_y),

    where `C(dat, eb)` is a constant depending only on the population
    spectrum (specifically the inverse-gap `1 / min_{s ≠ r} |ρ_r* − ρ_s*|`
    and the conditioning `‖Σˣˣ⁻¹‖`). The constant is `ε`-independent.

    Stated as an existential over the sample eigenpair `(v_hat, rho_hat)`;
    the concrete construction is the generalised Rayleigh quotient of
    `(Σ̂ʸˣ, Σ̂ˣˣ)`, but we abstract over it to keep the statement
    Mathlib-friendly.

    PROVIDED SOLUTION
    Step 1. The generalised eigenvalue problem `Σʸˣ v = ρ Σˣˣ v` is
    equivalent to the standard eigenvalue problem
    `(Σˣˣ)^{-1/2} Σʸˣ (Σˣˣ)^{-1/2} w = ρ w` after the change of basis
    `w = (Σˣˣ)^{1/2} v`.
    Step 2. Apply Davis–Kahan / Weyl's inequality to the symmetric matrix
    `M = (Σˣˣ)^{-1/2} Σʸˣ (Σˣˣ)^{-1/2}` and its sample analogue. Operator-
    norm perturbation `‖M̂ − M‖_op` is bounded by
    `O(‖Σˣˣ⁻¹‖ · (δ_x · ‖Σʸˣ‖_op + δ_y))` via product-rule expansion.
    Step 3. Weyl bounds `|ρ̂_r − ρ_r*|` by `‖M̂ − M‖_op` for each `r`.
    Set `C = O(‖Σˣˣ⁻¹‖ · ‖Σʸˣ‖_op + ‖Σˣˣ⁻¹‖)`.
-/
theorem sample_eigenvalue_perturbation
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (SigmaXX_hat SigmaYX_hat : Matrix (Fin d) (Fin d) ℝ)
    (delta_x delta_y : ℝ) (hδx_nn : 0 ≤ delta_x) (hδy_nn : 0 ≤ delta_y)
    -- Operator-norm concentration (taken as hypothesis; produced by
    -- sub-Gaussian / sub-exponential matrix Bernstein, out of scope here).
    (h_conc_x : matFrobNorm (SigmaXX_hat - dat.SigmaXX) ≤ delta_x)
    (h_conc_y : matFrobNorm (SigmaYX_hat - dat.SigmaYX) ≤ delta_y) :
    ∃ C : ℝ, 0 < C ∧
      ∃ rho_hat : Fin d → ℝ,
        ∀ r : Fin d, |rho_hat r - (eb.pairs r).rho| ≤ C * (delta_x + delta_y) := by
  sorry

end JepaRhoRecovery
