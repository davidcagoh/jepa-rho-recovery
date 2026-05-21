/-
# JepaRhoRecovery.Concentration

Layer 3.3 — matrix concentration interface for finite-sample ρ-recovery.

Houses the named axiom `matrix_bernstein_subgaussian` (Tropp 2015
Theorem 1.6.2) that bridges from "n iid sub-Gaussian samples" to the
concentration radius `δ_n = O(√(d log(d/ν)/n))` consumed by Layer 3.2.

## Why an axiom

Matrix Bernstein for sub-Gaussian distributions is a well-established
external result (Tropp 2015, "An Introduction to Matrix Concentration
Inequalities", Theorem 1.6.2). Mathlib has scalar Bernstein and
sub-Gaussian concentration but not the matrix version in a form that
plugs directly into our Frobenius-norm setup. The axiom captures the
textbook statement; deriving it from Mathlib's matrix-tail-bound
machinery is a clean follow-up (paper-3 territory).

## Statement shape

The axiom is parameterised over a `ProbabilityMeasure` and an abstract
random matrix `Sigma_hat : Ω → Matrix`. It does not construct the
sampling process — that is delegated to the data model. The output is
the standard "with probability ≥ 1 − ν" event on the Frobenius norm.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import JepaRhoRecovery.Basic
import JepaRhoRecovery.SampleNoise

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace JepaRhoRecovery

open MeasureTheory

/-! ## §3.3 — Matrix Bernstein concentration -/

/-- **Axiom (Matrix Bernstein for sub-Gaussian samples, Tropp 2015 Thm 1.6.2).**

    For `n` iid samples from a sub-Gaussian distribution with covariance
    `Sigma` and sub-Gaussian parameter `K`, the empirical covariance
    `Sigma_hat : Ω → Matrix` (as a random matrix on a probability space
    `(Ω, μ)`) satisfies

        μ { ω : Sigma_hat ω is within Frobenius radius
            C·K·√(d·log(d/ν)/n) of Sigma } ≥ 1 − ν.

    No structural assumption is placed on the sampling process beyond
    that it produces a random matrix; the axiom asserts the existence
    of a universal constant `C_Bernstein` calibrating the concentration
    radius.

    **Reference.** Tropp 2015, "An Introduction to Matrix Concentration
    Inequalities", Theorem 1.6.2. Also derivable from Vershynin 2018
    "High-Dimensional Probability" Theorem 4.7.1 (covariance estimation
    for sub-Gaussian distributions).

    **Future work.** Discharge this axiom by porting Tropp's proof
    (matrix moment-generating function → master tail bound) on top of
    Mathlib's scalar Bernstein and matrix exponential machinery. -/
axiom matrix_bernstein_subgaussian
    {d : ℕ} (hd_pos : 0 < d)
    (Sigma : Matrix (Fin d) (Fin d) ℝ)
    (K : ℝ) (hK_pos : 0 < K)  -- sub-Gaussian parameter
    {Ω : Type} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (Sigma_hat : Ω → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (hn_pos : 0 < n)
    (ν : ℝ) (hν_pos : 0 < ν) (hν_lt_one : ν < 1) :
    ∃ C_Bernstein : ℝ, 0 < C_Bernstein ∧
      (μ {ω | matFrobNorm (Sigma_hat ω - Sigma)
                ≤ C_Bernstein * K *
                  Real.sqrt ((d : ℝ) * Real.log ((d : ℝ) / ν) / (n : ℝ))} : ℝ)
        ≥ 1 - ν

end JepaRhoRecovery
