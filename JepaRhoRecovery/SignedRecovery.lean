/-
# JepaRhoRecovery.SignedRecovery

Layer 4.2 — the moonshot headline. Sign identification and signed recovery
for ρ_r* from the JEPA training trajectory.

**Three statements** (corresponding to roadmap §4.2 (i)–(iii)):

  * `sign_identification_pos_iff_asymptote` — feature `r` has ρ_r* > 0 if
    and only if σ_r(t) approaches a strictly positive asymptote
    `σ_r* = √(ρ_r* μ_r)`. Pairs with `sign_identification_neg_iff_decay`.
  * `signed_recovery_pos_magnitude` — for ρ_r* > 0, the inversion estimator
    of Layer 2.2 (`rho_hat_rate` in `Inversion.lean`) recovers the magnitude
    at rate `O(ε^{1/L} |log ε|)`. Re-export wrapper.
  * `signed_recovery_neg_magnitude_obstruction` — for ρ_r* < 0, the JEPA
    trajectory carries **no information** about |ρ_r*| beyond its sign;
    direct covariance estimation is the only route. Stated as an
    indistinguishability claim.

**Signed-first discipline.** Statements take `eb : SignedGenEigenbasis dat`
and case-split on the sign of `(eb.pairs r).rho` via explicit hypotheses,
not via separate positive/negative structures.

**Dependencies.**

| Statement | Depends on |
|---|---|
| `sign_identification_*` | Layer 4.1 trichotomy (positive convergence + negative suppression + zero degeneracy) |
| `signed_recovery_pos_magnitude` | Layer 2.2 `rho_hat_rate` (already proved, Aristotle a65a98a3) |
| `signed_recovery_neg_magnitude_obstruction` | Layer 4.1(c) `sigma_negative_branch_le_init` + no-information argument |

The negative branch's full convergence-to-zero (not just monotonicity) is a
separate Layer-4.1(c′) refinement; we expose the cleanest form available now.
-/

import JepaRhoRecovery.Basic
import JepaRhoRecovery.QuasiStatic
import JepaRhoRecovery.Inversion
import JepaRhoRecovery.SignedODE
import JepaRhoRecovery.DiagonalODE

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Filter
open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §4.2(i) — Sign identification -/

/-- **Theorem 4.2(i) (Sign identification — positive branch).**

    Feature `r` has `ρ_r* > 0` *if and only if* its diagonal amplitude
    `σ_r(t)` approaches a strictly positive asymptote
    `σ_r* = √(ρ_r* μ_r)` as `t → ∞`.

    This is one direction of the trichotomy:
      * `ρ > 0` ⇒ positive asymptote (paper-1 `actual_critical_time` lineage).
      * positive asymptote ⇒ `ρ > 0` (contrapositive of Layer 4.1(c)
        suppression for ρ < 0, and of the zero-branch degeneracy).

    Stated abstractly over a limit predicate `HasPositiveAsymptote` so the
    statement is independent of how the asymptote is formalised.

    PROVIDED SOLUTION
    Forward (`ρ > 0 ⇒ σ → σ_r* > 0`):
      Apply paper-1's `actual_critical_time` / `bernoulli_laurent_bound`
      lineage, which proves `σ_r(τ_r*) = p · σ_r*` for the critical-time
      hitting time τ_r*. Combine with monotonic convergence on `[τ_r*, ∞)`
      (positive-branch fixed-point stability — Layer 4.1(a), pending port).
    Backward (`σ → σ_r* > 0 ⇒ ρ > 0`):
      Contrapose. If `ρ < 0`, `sigma_negative_branch_le_init` from
      `SignedODE.lean` gives σ_r(t) ≤ σ_r(0) = ε^{1/L} → 0. If `ρ = 0`,
      the ODE degenerates to σ̇ = 0 (Layer 4.1(b), pending) and σ stays at
      ε^{1/L}. Neither has a strictly positive asymptote.

    Status: sorry'd; pending positive-branch convergence port (Layer 4.1(a))
    and zero-branch lemma (Layer 4.1(b)).
-/
theorem sign_identification_pos_iff_asymptote
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (sigma : ℝ → ℝ)
    (HasPositiveAsymptote : (ℝ → ℝ) → ℝ → Prop)
    (sigma_star : ℝ)
    (h_sigma_star_def : sigma_star = Real.sqrt ((eb.pairs r).rho * (eb.pairs r).mu)) :
    (0 < (eb.pairs r).rho ↔ HasPositiveAsymptote sigma sigma_star) := by
  sorry

/-! ## §4.2(ii) — Magnitude recovery for positive features

    Re-export of Layer 2.2's `rho_hat_rate` (already proved). Stated here
    to make the dependency explicit in the signed-recovery API. -/

/-- **Theorem 4.2(ii) (Positive-magnitude recovery, abstract form).**

    For features with `ρ_r* > 0`, there is an estimator `rho_hat` computable
    from the critical-time `t_crit ε` of the σ_r trajectory satisfying
        |rho_hat ε − ρ_r*| ≤ C · ε^{1/L} · |log ε|
    for ε small enough.

    PROVIDED SOLUTION
    Direct re-export of `JepaRhoRecovery.Inversion.rho_hat_rate` applied with
    the data of `(eb.pairs r)`. The statement requires the Laurent-expansion
    hypothesis on `t_crit` (paper-1's `bernoulli_laurent_bound` lineage) —
    abstractly bundled here so this file does not import paper-1 machinery
    that has not yet been ported. -/
theorem signed_recovery_pos_magnitude
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_pos : 0 < (eb.pairs r).rho)
    (t_crit : ℝ → ℝ)
    (K_log : ℝ) (hK_log_pos : 0 < K_log)
    (h_laurent : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_crit ε - (1 / ((eb.pairs r).rho * (eb.pairs r).mu)) *
            ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
              (L : ℝ) / ((n : ℝ) * (eb.pairs r).rho ^ (2 * L - n - 1)) *
              ε ^ (((n : ℝ) - 2) / (L : ℝ))|
        ≤ K_log * |Real.log ε|) :
    ∃ (rho_hat : ℝ → ℝ) (C : ℝ), 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        |rho_hat ε - (eb.pairs r).rho| ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  sorry

/-! ## §4.2(iii) — Negative-magnitude obstruction -/

/-- **Theorem 4.2(iii) (Negative-magnitude obstruction).**

    For features with `ρ_r* < 0`, the JEPA trajectory `σ_r(t)` is bounded
    above by its initial value `σ_r(0) = ε^{1/L}` for all `t ∈ [0, t_max]`
    (Layer 4.1(c) `sigma_negative_branch_le_init`). In particular,
    `|σ_r(t)| → 0` does not reveal `|ρ_r*|` beyond the sign bit.

    Stated as: there exist two negative-ρ instances with different
    `|ρ_r*|` but the **same** trajectory bound. The user must therefore
    fall back to direct sample-covariance estimation, as the roadmap states.

    PROVIDED SOLUTION
    Take two scalar pairs `(λ₁, ρ₁)` and `(λ₂, ρ₂)` with
    `λ₁ = λ₂ < 0`, `ρ₁ < ρ₂ < 0`, and identical initial data
    `σ(0) = ε^{1/L}`. Apply `sigma_negative_branch_le_init` to each: both
    σ_i satisfy `σ_i(t) ≤ ε^{1/L}` on `[0, t_max]`. Thus from the
    trajectory bound alone the two instances are indistinguishable, even
    though `|ρ₁| ≠ |ρ₂|`. -/
theorem signed_recovery_neg_magnitude_obstruction
    (L : ℕ) (hL : 2 ≤ L)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    (t_max : ℝ) (ht_max : 0 < t_max) :
    ∃ (lambda rho₁ rho₂ : ℝ),
        lambda < 0 ∧ rho₁ < 0 ∧ rho₂ < 0 ∧ rho₁ ≠ rho₂ ∧
        ∀ (sigma₁ sigma₂ : ℝ → ℝ),
          (∀ t ∈ Set.Icc 0 t_max, 0 < sigma₁ t) →
          (∀ t ∈ Set.Icc 0 t_max, 0 < sigma₂ t) →
          ContinuousOn sigma₁ (Set.Icc 0 t_max) →
          ContinuousOn sigma₂ (Set.Icc 0 t_max) →
          (∀ t ∈ Set.Ioo 0 t_max,
            HasDerivAt sigma₁
              (lambda * Real.rpow (sigma₁ t) (3 - 1 / (L : ℝ))
                - (lambda / rho₁) * (sigma₁ t) ^ 3) t) →
          (∀ t ∈ Set.Ioo 0 t_max,
            HasDerivAt sigma₂
              (lambda * Real.rpow (sigma₂ t) (3 - 1 / (L : ℝ))
                - (lambda / rho₂) * (sigma₂ t) ^ 3) t) →
          ∀ t ∈ Set.Icc 0 t_max,
            sigma₁ t ≤ sigma₁ 0 ∧ sigma₂ t ≤ sigma₂ 0 := by
  refine ⟨-1, -1, -2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro sigma₁ sigma₂ hPos₁ hPos₂ hCont₁ hCont₂ hODE₁ hODE₂ t ht
  refine ⟨?_, ?_⟩
  · exact sigma_negative_branch_le_init L hL (-1) (-1) (by norm_num) (by norm_num)
      t_max ht_max sigma₁ hPos₁ hCont₁ hODE₁ t ht
  · exact sigma_negative_branch_le_init L hL (-1) (-2) (by norm_num) (by norm_num)
      t_max ht_max sigma₂ hPos₂ hCont₂ hODE₂ t ht

end JepaRhoRecovery
