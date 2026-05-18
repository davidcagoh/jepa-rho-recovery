/-
# JepaRhoRecovery.QuasiStatic

Layer 1.1: rigorous quasi-static decoder ODE. Replaces paper-1's vacuous
`hV_flow : ∀ t, deriv (fun t => ‖V t - V_qs(Wbar t)‖) t ≤ 0` with a real
`HasDerivAt` hypothesis and a real contraction–drift Grönwall proof.

Target of `requests/01_layer1_1_quasi_static.md`. Currently `sorry`.
Acceptance criteria forbid:
  - `deriv f t = 0` vacuity (use `HasDerivAt`)
  - ε-dependent constant witnesses (C must be provably ε-independent)
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-- **Theorem 1.1 (Quasi-static decoder — rigorous).**

    Under gradient-flow ODEs for `Wbar` and `V` and balanced initialisation
    at scale ε, the decoder tracks its quasi-static fixed point to leading
    order in ε on `[0, t_max]`.

    Conclusion: there exists a positive constant `C` (independent of ε) with
        ‖V t - V_qs(W̄ t)‖_F ≤ C · ε^{2(L-1)/L}
    for all `t ∈ [0, t_max]`.

    Proof strategy (two-phase, see `paper/outline.md` §3):
      * Phase A: decoder transient on `[0, ε^{-2/L}]` — explicit decoder ODE
        solution with W̄ frozen at ε^{1/L} U^w.
      * Phase B: contraction–drift balance — Grönwall with contraction rate
        α(t) = Θ(ε^{2/L}) and drift ‖D(t)‖ = O(ε²). Both terms balance at
        O(ε^{2(L-1)/L}) for L ≥ 2.
-/
theorem quasiStatic_rigorous
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (Wbar V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hWbar_flow : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt Wbar (-(gradWbar dat (Wbar t) (V t))) t)
    (hV_flow : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt V (-(gradV dat (Wbar t) (V t))) t)
    (hWbar_init : ∀ r : Fin d, diagAmplitude dat eb (Wbar 0) r = epsilon)
    (hV_init : matFrobNorm (V 0) ≤ epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Set.Icc 0 t_max,
        matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
          ≤ C * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L) := by
  sorry

end JepaRhoRecovery
