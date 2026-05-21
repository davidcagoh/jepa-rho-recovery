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

/-- **Theorem 3.2′ (Plateau-path finite-sample ρ-recovery, positive branch).**

    Given:
      * A sample-side observation-time function `T_hat : ℝ → ℝ` and the
        corresponding sample trajectory value `σ̂(ε) := σ_n(T_hat(ε))`,
        satisfying the plateau bound
          `|σ̂(ε) − ρ̂_pop^L| ≤ K_plateau · ε^{1/L} · |log ε|`
        from `signed_recovery_pos_magnitude_plateau` applied to the
        sample-side trajectory (with sample-side `ρ̂_pop`).
      * A sample-eigenvalue perturbation bound
          `|ρ̂_pop − ρ_r*| ≤ δ_n`
        from `sample_eigenvalue_perturbation` (Layer 3.1).

    Conclusion: the plateau-derived estimator `ρ̂_n(ε) := σ̂(ε)^{1/L}`
    satisfies, for ε in a positive sub-window,
        `|ρ̂_n(ε) − ρ_r*| ≤ C_ε · ε^{1/L} · |log ε| + δ_n`. -/
-- ⚠ DEPRECATED (session 90, 2026-05-21). Inherits inverted-form ρ̂ := σ^(1/L)
--   from plateau_path_recovery_pos. Corrected finite-sample composition uses
--   ρ̂ := σ^L. Preserved as historical.
@[deprecated "Inverted ODE form; use a corrected composition built on Corrected.* theorems"]
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

/-- **Theorem (Plateau-path finite-sample rate — high-probability form).**

    Pure measure-theoretic lift: given a measurable "good event" `G`
    with `μ(G) ≥ 1 − ν` on which the deterministic finite-sample rate
    holds pointwise, the rate holds with probability ≥ `1 − ν`.

    The deterministic rate hypothesis `h_rate_on_G` is what the
    composition pattern above produces; the matrix-Bernstein axiom and
    `sample_eigenvalue_perturbation` are invoked outside this theorem
    so the signature stays clean. -/
-- ⚠ DEPRECATED (session 90, 2026-05-21). High-probability wrapper around the
--   inverted-form plateau_path_finite_sample_rate_pos. Preserved as historical.
@[deprecated "Inverted ODE form; build a corrected high-prob wrapper on Corrected.* theorems"]
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

end JepaRhoRecovery
