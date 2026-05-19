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

end JepaRhoRecovery
