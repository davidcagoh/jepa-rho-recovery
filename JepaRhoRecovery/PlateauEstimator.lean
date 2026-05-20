/-
# JepaRhoRecovery.PlateauEstimator

Layer 2.2′ — **plateau-based and early-slope-based identifiability** for the
positive branch. These two abstract analytic lemmas underpin the
pure-trajectory recovery story (paper §5 Thm 5.1′ and Thm 5.2).

## Two estimators, one trajectory

The diagonal Bernoulli ODE
    σ̇_r = λ_r* · σ_r^{3-1/L} - μ_r · σ_r^3
has two free parameters (λ_r*, μ_r) and the positive-branch trajectory
exposes them through two STRUCTURALLY INDEPENDENT observables:

  * **Plateau** σ_r^∞ = (ρ_r*)^L (set σ̇ = 0 ⇒ σ_r^{1/L} = λ_r*/μ_r = ρ_r*).
    Identifies the RATIO ρ_r* = λ_r*/μ_r alone, **without separate
    knowledge of λ_r* or μ_r**, hence WITHOUT covariance side-channel.
  * **Early-time slope.** For σ_r ≪ 1, the σ_r^3 term is dominated by
    σ_r^{3-1/L} by factor σ_r^{-1/L} ≥ ε^{-1/L}. So σ̇_r ≈ λ_r* σ_r^{3-1/L},
    which integrates explicitly. Identifies λ_r* ALONE (μ_r absent at
    leading order).

Combining the two recovers (λ_r*, μ_r) jointly from one trajectory.

## File contents

  * `rho_hat_plateau_rate` — given a plateau-approach hypothesis
    `|σ(T(ε)) - ρ^L| ≤ K · ε^{1/L} · |log ε|`, the plateau estimator
    `σ(T)^{1/L}` recovers `ρ` at rate O(ε^{1/L} |log ε|).
  * `lambda_hat_early_slope_rate` — given the early-time σ-bound
    `|σ(t₀) - σ_idealised(t₀)| ≤ K · ε^{1/L}` for σ_idealised solving the
    μ = 0 ODE, the slope estimator
    `λ̂(ε) := (L/(2L-1)) · (ε^{-(2L-1)/L} - σ(t₀)^{-(2L-1)/L}) / t₀`
    recovers `λ` at rate O(ε^{1/L} |log ε|).

## Pattern

These follow `Inversion.rho_hat_rate`'s pattern: take the trajectory→Laurent
or trajectory→plateau bound as a HYPOTHESIS (proved separately by the
JEPA-dynamics chain in `SignedRecovery.lean` and the ODE bridges of
`SignedODE.lean`), and produce the estimator rate by a self-contained
analytic argument. The HARD ODE work is in the bridge lemmas; THIS file
is the Lipschitz/monotonicity/algebraic-reduction part.

## Vacuity discipline

Per `CLAUDE.md`:
  * `ε_0 > 0` and `C > 0` are forced existentials; vacuous `ε_0 = 0` or
    `C = 0` witnesses violate the contract.
  * Hypotheses `h_plateau_bound` / `h_early_slope_bound` MUST be used —
    proofs that ignore them are degenerate and rejected.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Finset Filter
open scoped Matrix

namespace JepaRhoRecovery

/-! ## §5.1′ — Plateau estimator (positive branch)

    From the convergence `σ_r(t) → (ρ_r*)^L` (proved sorry-free as
    `SignedODE.sigma_positive_branch_converges`, Aristotle `22e700ca`),
    upgraded to a quantitative rate of approach, the plateau estimator
    `σ_r(T)^{1/L}` recovers ρ_r* with no covariance input. -/

/-- **Theorem 5.1′ (Plateau estimator, abstract form).**

    Suppose `σ_at_T` is a function of `ε` representing the observed
    plateau value σ_r(T(ε)) at a sufficiently late time T(ε), and we
    have the plateau-approach bound

        |σ_at_T ε - ρ^L| ≤ K_plateau · ε^{1/L} · |log ε|     (∀ ε ∈ (0,1)).

    Then the **plateau estimator** `ρ̂_plateau(ε) := (σ_at_T ε)^{1/L}`
    satisfies

        |ρ̂_plateau ε - ρ| ≤ C · ε^{1/L} · |log ε|

    for all `ε ∈ (0, ε_0)`, with explicit positive ε_0, C depending on
    `L, ρ, K_plateau` only.

    PROVIDED SOLUTION (3 steps).

    Step 1 (positivity of `σ_at_T ε`). For ε small enough,
        |σ_at_T ε - ρ^L| ≤ K · ε^{1/L} · |log ε| < ρ^L / 2
    forces σ_at_T ε ∈ (ρ^L/2, 3ρ^L/2), in particular > 0. Choose
    ε_0 small enough to ensure this: solve K · ε^{1/L} · |log ε| < ρ^L/2
    via a coarse upper bound `|log ε| ≤ ε^{-1/(2L)}` for ε ∈ (0, ε_*)
    (some explicit ε_*), then `K · ε^{1/(2L)} < ρ^L/2` gives ε_0.

    Step 2 (Lipschitz of `x ↦ x^{1/L}` near `ρ^L`). On the interval
    `[ρ^L/2, 3ρ^L/2]`, `x ↦ x^{1/L}` is C¹ with derivative
        d/dx [x^{1/L}] = (1/L) · x^{1/L - 1}.
    Its maximum on this interval is at the left endpoint:
        (1/L) · (ρ^L/2)^{1/L - 1} = (1/L) · ρ^{1-L} · 2^{1-1/L}.
    By the mean value theorem,
        |(σ_at_T ε)^{1/L} - ρ| = |(σ_at_T ε)^{1/L} - (ρ^L)^{1/L}|
          ≤ (1/L) · ρ^{1-L} · 2^{1-1/L} · |σ_at_T ε - ρ^L|.

    Step 3 (combine). Set `C := (1/L) · ρ^{1-L} · 2^{1-1/L} · K_plateau`.
    Then |ρ̂_plateau ε - ρ| ≤ C · ε^{1/L} · |log ε|. `C > 0` since each
    factor is positive.

    Mathlib hooks: `Real.rpow_natCast`, `Real.rpow_div_natCast`,
    `Real.hasDerivAt_rpow_const`, `Convex.norm_image_sub_le_of_norm_deriv_le_segment`
    (or hand-written mean-value bound on a closed interval). The `|log ε|`
    factor multiplies through without further analysis.

    The hypothesis `h_plateau_bound` MUST be used — a vacuous proof
    (e.g. setting `ρ̂_plateau := ρ`) is forbidden by the witness
    structure: the estimator value is `(σ_at_T ε)^{1/L}`, not a free
    function. -/
theorem rho_hat_plateau_rate
    (L : ℕ) (hL : 2 ≤ L)
    (rho : ℝ) (hrho_pos : 0 < rho)
    (sigma_at_T : ℝ → ℝ)
    (K_plateau : ℝ) (hK_plateau_pos : 0 < K_plateau)
    (h_plateau_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma_at_T ε - rho ^ L| ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |Real.rpow (sigma_at_T ε) ((1 : ℝ) / L) - rho|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry

/-! ## §5.2 — Early-time slope estimator for λ_r* (positive branch)

    For ε small enough that `σ_r(t)` is much smaller than its plateau on
    `[0, t₀]`, the μ_r σ_r^3 term is dominated by λ_r* σ_r^{3-1/L}
    uniformly. Integrating `σ̇ = λ σ^{3-1/L}` from σ(0)=ε to σ(t₀):

        d/dt [-(L/(2L-1)) σ^{-(2L-1)/L}] = λ
      ⇒  σ(t₀)^{-(2L-1)/L} - ε^{-(2L-1)/L} = -((2L-1)/L) · λ · t₀
      ⇒  λ = (L/(2L-1)) · (ε^{-(2L-1)/L} - σ(t₀)^{-(2L-1)/L}) / t₀.

    The μ_r perturbation is controlled by Grönwall as an O(ε^{1/L})
    correction (the μ term contributes at most a factor 1+O(ε^{1/L})
    to the integral since σ ≤ a constant times ε^{1/L} times the ideal
    on [0, t₀]). -/

/-- **Theorem 5.2 (Early-time slope estimator for λ_r*, abstract form).**

    Suppose `sigma_at_t0 : ℝ → ℝ` represents the observed value
    σ_r(t₀(ε)) at the early time `t₀(ε) := c · λ⁻¹ · ε^{-(2L-1)/L}`
    for some fixed constant `0 < c < 1`, and we have the early-time bound

        |sigma_at_t0 ε - sigma_idealised ε| ≤ K_early · ε^{1/L} · |log ε|

    where `sigma_idealised ε := (ε^{-(2L-1)/L} - ((2L-1)/L) · λ · t₀(ε))^{-L/(2L-1)}`
    is the solution to the idealised (μ = 0) Bernoulli ODE.

    Then the **early-slope estimator**

        λ̂(ε) := (L/(2L-1)) · (ε^{-(2L-1)/L} - (sigma_at_t0 ε)^{-(2L-1)/L}) / t₀(ε)

    satisfies

        |λ̂ ε - λ| ≤ C · ε^{1/L} · |log ε|

    for all `ε ∈ (0, ε_0)`, with explicit positive ε_0, C depending on
    `L, λ, c, K_early` only.

    PROVIDED SOLUTION (4 steps).

    Step 1 (idealised inversion is exact). For the idealised σ_id,
        σ_id(t₀)^{-(2L-1)/L} = ε^{-(2L-1)/L} - ((2L-1)/L) λ t₀
      ⇒  λ = (L/(2L-1)) · (ε^{-(2L-1)/L} - σ_id(t₀)^{-(2L-1)/L}) / t₀.

    Step 2 (perturbation transfer). For `σ := sigma_at_t0 ε`,
        |σ^{-(2L-1)/L} - σ_id^{-(2L-1)/L}|
          ≤ ((2L-1)/L) · max(σ, σ_id)^{-(2L-1)/L - 1} · |σ - σ_id|
    by mean-value on `x ↦ x^{-(2L-1)/L}`. Both σ and σ_id are bounded
    above by their plateau (and below by ε; cf. positivity from
    h_early_slope_bound and the idealised lower bound).

    Step 3 (substitute t₀ scaling). t₀ = c · λ⁻¹ · ε^{-(2L-1)/L}, so
    `(λ̂ - λ) · t₀` is bounded by Step 2's expression and then dividing
    by t₀ gives an extra ε^{(2L-1)/L} multiplier that, combined with
    the ε^{1/L} from Step 2's mean-value (since σ is roughly ε^{1/L}
    on [0, t₀]), yields the ε^{1/L} · |log ε| rate.

    Step 4 (assemble explicit constant). Track each constant to extract
    `C(L, λ, c, K_early)`. Strict positivity inherited.

    Mathlib hooks: same as `rho_hat_plateau_rate` plus
    `Real.rpow_neg_one`, `Real.rpow_natCast`, `inv_sub_inv`, and
    `Convex.norm_image_sub_le_of_norm_deriv_le_segment` for the
    mean-value step on `x ↦ x^{-(2L-1)/L}`.

    The hypothesis `h_early_slope_bound` MUST be used (the estimator is
    a fixed formula in sigma_at_t0, not free). Vacuous solutions
    (e.g. setting `t₀ := 0` or `σ_at_t0 := σ_id`) are forbidden because:
      * `t₀` is a positional argument satisfying `0 < t₀`;
      * `σ_at_t0` is an arbitrary input, not constrained to equal σ_id. -/
theorem lambda_hat_early_slope_rate
    (L : ℕ) (hL : 2 ≤ L)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (sigma_at_t0 : ℝ → ℝ)
    (K_early : ℝ) (hK_early_pos : 0 < K_early)
    (h_early_slope_bound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        0 < sigma_at_t0 ε ∧
        |sigma_at_t0 ε
          - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / L)
                      - ((2 * (L : ℝ) - 1) / L) * lambda
                          * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L)))
                      (-L / (2 * (L : ℝ) - 1))|
          ≤ K_early * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε_0 →
          |((L : ℝ) / (2 * (L : ℝ) - 1))
              * (ε ^ (-(2 * (L : ℝ) - 1) / L)
                  - Real.rpow (sigma_at_t0 ε) (-(2 * (L : ℝ) - 1) / L))
              / (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L))
           - lambda|
            ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry

end JepaRhoRecovery
