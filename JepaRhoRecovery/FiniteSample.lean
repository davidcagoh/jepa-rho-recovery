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

import JepaRhoRecovery.Basic
import JepaRhoRecovery.SampleNoise
import JepaRhoRecovery.Inversion

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
    (r : Fin d) (hrho_pos : 0 < (eb.pairs r).rho)
    -- Sample-side hitting time satisfies a Laurent expansion.
    (t_crit_hat : ℝ → ℝ)
    (rho_hat_pop : ℝ)  -- population-side sample-eigenvalue estimate ρ̂_r*
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
    ∃ (rho_estimator : ℝ → ℝ) (C_eps C_n : ℝ), 0 < C_eps ∧ 0 < C_n ∧
      ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        |rho_estimator ε - (eb.pairs r).rho|
          ≤ C_eps * ε ^ ((1 : ℝ) / L) * |Real.log ε| + C_n * delta_n := by
  sorry

end JepaRhoRecovery
