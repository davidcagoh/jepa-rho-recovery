/-
# JepaRhoRecovery.Inversion

Layer 2.2: identifiability — inversion formula recovering ρ* from the
critical time $\tilde t_r^*$. Pure asymptotic analysis; no ODE machinery.
First Aristotle target for the option-2 moonshot.

Positive-ρ branch only (the inversion formula's `ρ^{2L-2}` factors require
`0 < ρ`). The signed branch (Layer 4.2) will live in `SignedRecovery.lean`
and uses a different invariant — suppression timescale — for negative
features.

Proof source: `../../../jepa-learning-order/my_theorems/paper2_recovery/proof_lecture.md`
Theorem 2.1, lines 131–248.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

/-- **Theorem 2.2 (Identifiability inversion formula).**

    Given the Laurent expansion of the critical time
    $\tilde t_r^* = (1/\lambda)\sum_{n=1}^{2L-1} L/(n\,\rho^{2L-n-1}\,\epsilon^{n/L})
                  + \Theta(\log\epsilon)$
    (paper-1 Corollary 6.2), the leading-order inversion estimator
        ρ̂(ε) := (L / (λ · t_crit ε · ε^{1/L}))^{1/(2L-2)}
    recovers `ρ` at rate `O(ε^{1/L} |log ε|)` as `ε → 0⁺`.

    PROVIDED SOLUTION (from proof_lecture.md Theorem 2.1, 4 steps).

    Step 1 (Isolate the n = 1 term).  Multiply the Laurent identity
    `h_laurent` through by `λ · ε^{1/L}`:
        λ · t_crit ε · ε^{1/L}
          = Σ_{n=1}^{2L-1} L/(n · ρ^{2L-n-1}) · ε^{(n-1)/L}
            + ε^{1/L}·λ·Θ(log ε).
    Separate n = 1 from the remainder. Set
        A     := L / ρ^{2L-2}              -- positive, ε-independent
        δ(ε)  := Σ_{n=2}^{2L-1} L/(n · ρ^{2L-n-1}) · ε^{(n-1)/L}
                 + λ · ε^{1/L} · (log-tail).
    Then  λ · t_crit ε · ε^{1/L} = A + δ(ε).

    Step 2 (Remainder bound).  For n ≥ 2 we have (n-1)/L ≥ 1/L > 0, so
    `ε^{(n-1)/L} ≤ ε^{1/L}` for `ε ∈ (0,1)`. The log-tail contributes
    `K_log · λ · ε^{1/L} · |log ε|`. Hence
        |δ(ε)| ≤ D · ε^{1/L} · |log ε|
    with
        D_0 := Σ_{n=2}^{2L-1} L · ρ^{n+1-2L} / n      -- positive, ε-indep
        D   := D_0 + K_log · λ                         -- positive, ε-indep
    (Use `|log ε| ≥ 1` for `ε ∈ (0, 1/e)` to absorb the n ≥ 2 sum into
    the log factor — pick `ε_0 ≤ 1/e` below to make this valid.)

    Step 3 (Invert to bound `ρ̂^{2L-2} - ρ^{2L-2}`).
    By construction `ρ̂^{2L-2} = L / (λ · t_crit ε · ε^{1/L}) = L / (A + δ)`.
    Rewrite `L/(A + δ) = (L/A) · 1/(1 + δ/A) = ρ^{2L-2} · 1/(1 + δ/A)`.

    Pick ε_0 such that `D · ε_0^{1/L} · |log ε_0| ≤ A/2`, so for
    `ε ∈ (0, ε_0)` we have `|δ/A| ≤ 1/2`. Using `|1/(1+u) - 1| ≤ 2|u|`
    when `|u| ≤ 1/2`:
        |ρ̂^{2L-2} - ρ^{2L-2}|
          = ρ^{2L-2} · |1/(1+δ/A) - 1|
          ≤ ρ^{2L-2} · 2 · |δ|/A
          = (2ρ^{2L-2} · ρ^{2L-2} / L) · |δ|
          ≤ B_0 · ε^{1/L} · |log ε|
    with `B_0 := (2ρ^{2(2L-2)} / L) · D`.

    Step 4 (Mean value on `g(x) = x^{1/(2L-2)}`).
    `g'(x) = (1/(2L-2)) · x^{-(2L-3)/(2L-2)}` is decreasing on `(0,∞)`,
    so `|g'(ξ)|` is maximised at the smaller endpoint. From Step 3 with
    `|δ/A| ≤ 1/2`, `ρ̂^{2L-2} ≥ ρ^{2L-2}/2`. Hence for ξ between the
    two values,
        |g'(ξ)| ≤ (1/(2L-2)) · (ρ^{2L-2}/2)^{-(2L-3)/(2L-2)}
               = 2^{(2L-3)/(2L-2)} / ((2L-2) · ρ^{2L-3}).
    MVT gives
        |ρ̂ - ρ| ≤ |g'(ξ)| · |ρ̂^{2L-2} - ρ^{2L-2}|
              ≤ C · ε^{1/L} · |log ε|
    with
        C := (2^{(2L-3)/(2L-2)} / ((2L-2) · ρ^{2L-3})) · B_0 + 1
    (the `+1` guarantees `0 < C`).

    Witness for the existentials:
        ε_0 := min(1/(2·Real.exp 1),
                   ((A / (2·D))^L) · (1 / (|log (A/(2D))| + 1)))
    or any positive value satisfying the Step-3 inequality. Both `ε_0`
    and `C` depend only on `(L, ρ, λ, K_log)`, never on `t_crit` or `ε`.

    The construction is *constructive*: every constant `A`, `D_0`, `D`,
    `B_0`, `C`, `ε_0` is a closed-form function of `(L, ρ, λ, K_log)`.
    A vacuous witness (`ε_0 = 0`, `C` depending on `ε`) does not satisfy
    the conjunction `0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧ ∀ ε ∈ (0, ε_0), ...`. -/
theorem rho_hat_rate
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hrho_pos : 0 < rho) (hlambda_pos : 0 < lambda)
    (t_crit : ℝ → ℝ)
    (K_log : ℝ) (hK_log_pos : 0 < K_log)
    (h_laurent : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_crit ε - (1 / lambda) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
            (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1) * ε ^ ((n : ℝ) / L))|
        ≤ K_log * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε_0 →
        |Real.rpow ((L : ℝ) / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L)))
                   (1 / (2 * (L : ℝ) - 2))
         - rho|
          ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry

end JepaRhoRecovery
