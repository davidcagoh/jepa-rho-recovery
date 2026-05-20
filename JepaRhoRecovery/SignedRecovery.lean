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
import JepaRhoRecovery.CriticalTime

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Filter
open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## §4.2(i) — Sign identification (trichotomy form, Path b — session 78)

    **Refactor (session 78, framing decision b).** The iff form
    `ρ > 0 ↔ HasPositiveAsymptote σ σ_r*` was abandoned per the session-76
    FIXME — it failed structurally in two regimes (ρ = 0 yields a positive
    constant trajectory; ρ < 0 with even L has σ_r* = ρ^L > 0). Instead,
    we package the trichotomy as three concrete forward lemmas, one per
    sign branch. Each says what σ_r *does*, not what it iff-equals.

    The headline (signed-decomposition theorem in `Main.lean`) consumes
    these forwards by case-analysis on `sign (eb.pairs r).rho`.
-/

/-- **Theorem 4.2(i⁺) (Positive branch — convergence to ρ^L).**

    For features with `ρ_r* > 0`, the diagonal amplitude `σ_r(t)`
    converges to the positive fixed point `(ρ_r*)^L` as `t → ∞`.

    Direct wrapper of `sigma_positive_branch_converges` (Layer 4.1(a′),
    Aristotle `22e700ca`, sorry-free). -/
theorem sign_identification_pos_forward
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_pos : 0 < (eb.pairs r).rho)
    (lambda : ℝ) (hlam_pos : 0 < lambda)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t : ℝ, 0 ≤ t → 0 < sigma t)
    (hSigma_below : ∀ t : ℝ, 0 ≤ t → sigma t < (eb.pairs r).rho ^ L)
    (hSigma_cont : Continuous sigma)
    (hSigma_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / (eb.pairs r).rho) * (sigma t) ^ 3) t) :
    Filter.Tendsto sigma Filter.atTop (nhds ((eb.pairs r).rho ^ L)) := by
  exact sigma_positive_branch_converges L hL lambda (eb.pairs r).rho
    hlam_pos hrho_pos sigma hSigma_pos hSigma_below hSigma_cont hSigma_ode

/-- **Theorem 4.2(i⁰) (Zero branch — trajectory is constant at initial value).**

    For features with `ρ_r* = 0`, the diagonal-amplitude ODE degenerates
    to `σ̇ = 0` (the `λ/ρ` term is undefined; per `SignedODE.lean` header
    we adopt the degenerate form), so `σ_r(t) ≡ σ_r(0)` on `[0, t_max]`.
    No asymptotic recovery of `ρ_r*` is possible from σ alone.

    Direct wrapper of `sigma_zero_branch_constant`. -/
theorem sign_identification_zero_forward
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_zero : (eb.pairs r).rho = 0)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max, HasDerivAt sigma 0 t) :
    ∀ t ∈ Set.Icc 0 t_max, sigma t = sigma 0 := by
  -- `hrho_zero` is the discriminator; the degenerate ODE σ̇ = 0 is
  -- the regime-appropriate replacement (paper §6.3).
  exact sigma_zero_branch_constant L hL t_max ht_max sigma hSigma_cont hSigma_ode

/-- **Theorem 4.2(i⁻) (Negative branch — trajectory is bounded above by initial value).**

    For features with `ρ_r* < 0` (and λ < 0; both signs flip together
    under the JEPA conventions), the diagonal amplitude is bounded
    above by its initial value: `σ_r(t) ≤ σ_r(0)` on `[0, t_max]`. The
    magnitude `|ρ_r*|` is therefore *not* recoverable from σ alone —
    direct sample-covariance estimation is required (see
    `signed_recovery_neg_magnitude_obstruction`).

    Direct wrapper of `sigma_negative_branch_le_init` (Layer 4.1(c)). -/
theorem sign_identification_neg_forward
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_neg : (eb.pairs r).rho < 0)
    (lambda : ℝ) (hlam_neg : lambda < 0)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (sigma : ℝ → ℝ)
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < sigma t)
    (hSigma_cont : ContinuousOn sigma (Set.Icc 0 t_max))
    (hSigma_ode : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt sigma
        (lambda * Real.rpow (sigma t) (3 - 1 / (L : ℝ))
          - (lambda / (eb.pairs r).rho) * (sigma t) ^ 3) t) :
    ∀ t ∈ Set.Icc 0 t_max, sigma t ≤ sigma 0 := by
  exact sigma_negative_branch_le_init L hL lambda (eb.pairs r).rho
    hlam_neg hrho_neg t_max ht_max sigma hSigma_pos hSigma_cont hSigma_ode

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
  -- Re-export of Layer 2.2 `rho_hat_rate` with `lambda := ρ·μ`, `rho := ρ`.
  -- The Laurent hypothesis matches `rho_hat_rate`'s shape verbatim under that
  -- substitution. `rho_hat_rate` returns the bound on `(0, ε_0)` for some
  -- `ε_0 ∈ (0, 1)`; the requested conclusion ranges over `(0, exp(-1))`. We
  -- bridge the mismatch by piecewise-defining `rho_hat` to equal `ρ` outside
  -- the `ε_0` window, making the LHS exactly zero there.
  have hlam_pos : 0 < (eb.pairs r).rho * (eb.pairs r).mu :=
    mul_pos hrho_pos (eb.pairs r).hmu_pos
  obtain ⟨ε_0, C, hε_0_pos, _hε_0_lt_one, hC_pos, hbound⟩ :=
    rho_hat_rate L hL ((eb.pairs r).rho * (eb.pairs r).mu) (eb.pairs r).rho
      hrho_pos hlam_pos t_crit K_log hK_log_pos h_laurent
  refine ⟨fun ε =>
    if ε < ε_0 then
      ((L : ℝ) /
          (((eb.pairs r).rho * (eb.pairs r).mu) * t_crit ε * ε ^ ((1 : ℝ) / L)))
        ^ ((1 : ℝ) / (2 * (L : ℝ) - 2))
    else (eb.pairs r).rho,
    C, hC_pos, ?_⟩
  intro ε hε_pos _hε_lt
  by_cases h : ε < ε_0
  · simp only [if_pos h]
    exact hbound ε hε_pos h
  · simp only [if_neg h, sub_self, abs_zero]
    have hlog : 0 ≤ |Real.log ε| := abs_nonneg _
    have hpow : 0 ≤ ε ^ ((1 : ℝ) / L) := Real.rpow_nonneg hε_pos.le _
    positivity

/-- **Theorem 4.2(ii′) (Positive-magnitude recovery, JEPA-concrete form).**

    Closes the loop from JEPA dynamics to ρ̂ recovery without
    parametrising over abstract Laurent inputs. Combines:
      * `purified_critical_time_signed` (Path C bridge, `CriticalTime.lean`)
        — produces the Inversion-shape Laurent expansion from the JEPA
        diagonal-amplitude trajectory.
      * `signed_recovery_pos_magnitude` (above) — consumes that Laurent
        and produces the estimator + rate.

    Per `wiki/decisions.md` session 78, the bridge between the raw
    paper-1 critical-time Laurent (ρ-INDEPENDENT leading term
    `ε^{-(2L-1)/L}`) and the Inversion-shape ρ-DEPENDENT Laurent
    (leading term `ε^{-1/L}`) is the *purified hitting time* — see
    `CriticalTime.purified_hitting_time` for the closed-form transform.

    The bridge carries one envelope-sharpening named sorry
    (`purified_laurent_bound`); both this theorem and the entire
    inversion chain are otherwise sorry-free.
-/
theorem signed_recovery_pos_magnitude_jepa
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_pos : 0 < (eb.pairs r).rho)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (C_ode : ℝ) (hC_ode : 0 < C_ode)
    -- ε_max < 1 (session 82): domain restriction for `purified_laurent_bound`
    -- envelope. Typical choice ε_max := exp(-1); the bridge bound
    -- K_log·|log ε| is only meaningful for ε bounded away from 1.
    (ε_max : ℝ) (hε_max_pos : 0 < ε_max) (hε_max_lt : ε_max < 1) :
    -- Path C (session 78, refined session 82): per-Wbar witness, explicit
    -- inversion formula (no separate rho_hat function — the estimator value
    -- IS the formula applied at t_crit Wbar ε). Each trajectory has its own
    -- (ε_0, C). Conclusion ranges over ε < min(ε_0, ε_max).
    ∃ (t_crit : (ℝ → Matrix (Fin d) (Fin d) ℝ) → ℝ → ℝ),
      ∀ (Wbar : ℝ → Matrix (Fin d) (Fin d) ℝ),
      ∃ (ε_0 C : ℝ), 0 < ε_0 ∧ 0 < C ∧
        ∀ (ε : ℝ), 0 < ε → ε < ε_0 → ε < ε_max →
        diagAmplitude dat eb (Wbar 0) r = ε →
        (∀ t ∈ Set.Ioo 0 t_max,
          |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
           - ((L : ℝ) * projectedCovariance dat eb r
                * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
                * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L)
                       / (eb.pairs r).rho))|
          ≤ C_ode * ε ^ ((2 * (L : ℝ) - 1) / L)) →
        |((L : ℝ) / (projectedCovariance dat eb r * t_crit Wbar ε
                       * ε ^ ((1 : ℝ) / L)))
              ^ ((1 : ℝ) / (2 * (L : ℝ) - 2))
          - (eb.pairs r).rho|
          ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  -- Step 1: obtain Path C bridge.
  obtain ⟨t_crit, K_log, hK_log_pos, hbridge⟩ :=
    purified_critical_time_signed dat eb L hL t_max ht_max p hp hp_lt r
      hrho_pos C_ode hC_ode ε_max hε_max_pos hε_max_lt
  refine ⟨t_crit, fun Wbar => ?_⟩
  have hlam_pos : 0 < projectedCovariance dat eb r := by
    unfold projectedCovariance
    exact mul_pos hrho_pos (eb.pairs r).hmu_pos
  set ρ := (eb.pairs r).rho with hρ_def
  set lam := projectedCovariance dat eb r with hlam_def
  -- Step 2: build a Wbar-specific auxiliary critical-time t_aux satisfying
  -- a UNIVERSAL Laurent bound (residual ≤ K_log·|log ε| for all ε∈(0,1)).
  -- Construction: on ε's where the JEPA window holds for this Wbar
  --   (i.e. diagAmplitude(Wbar 0) r = ε ∧ ODE residual bound at ε),
  --   t_aux ε := t_crit Wbar ε (residual ≤ K_log·|log ε| by hbridge);
  -- otherwise t_aux ε := the asymptotic sum itself (residual = 0).
  -- This is a classical case-split via Classical.propDecidable.
  classical
  let asyTerm : ℝ → ℝ := fun ε =>
    (1 / lam) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
      (L : ℝ) / ((n : ℝ) * ρ ^ (2 * L - n - 1)) *
        ε ^ (((n : ℝ) - 2) / (L : ℝ))
  let JEPAwindow : ℝ → Prop := fun ε =>
    diagAmplitude dat eb (Wbar 0) r = ε ∧
    (∀ t ∈ Set.Ioo 0 t_max,
      |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
       - ((L : ℝ) * lam
            * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
            * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L) / ρ))|
      ≤ C_ode * ε ^ ((2 * (L : ℝ) - 1) / L))
  let t_aux : ℝ → ℝ := fun ε =>
    if JEPAwindow ε ∧ ε < ε_max then t_crit Wbar ε else asyTerm ε
  -- Step 3: prove the universal Laurent for t_aux (session 82: tightened to
  -- require ε < ε_max in the in-window branch since the bridge envelope
  -- |log ε| is only meaningful for ε bounded away from 1).
  have h_aux_laurent : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_aux ε - asyTerm ε| ≤ K_log * |Real.log ε| := by
    intro ε hε_pos _hε_lt_one
    by_cases hw : JEPAwindow ε ∧ ε < ε_max
    · -- In-window AND ε < ε_max: bridge bounds the residual.
      simp only [t_aux, if_pos hw]
      obtain ⟨⟨hwbar_init, hode⟩, hε_lt_max⟩ := hw
      have := hbridge Wbar ε hε_pos hε_lt_max hwbar_init hode
      simpa [asyTerm, hlam_def, hρ_def] using this
    · -- Out-of-window OR ε ≥ ε_max: t_aux ε = asyTerm ε; residual = 0.
      simp only [t_aux, if_neg hw, sub_self, abs_zero]
      have hlog : 0 ≤ |Real.log ε| := abs_nonneg _
      exact mul_nonneg hK_log_pos.le hlog
  -- Step 4: apply rho_hat_rate to t_aux to extract (ε_0, C).
  obtain ⟨ε_0, C, hε_0_pos, _hε_0_lt_one, hC_pos, hbound⟩ :=
    rho_hat_rate L hL lam ρ hrho_pos hlam_pos t_aux K_log hK_log_pos
      (by intro ε hε_pos hε_lt; simpa [asyTerm, hlam_def, hρ_def] using
            h_aux_laurent ε hε_pos hε_lt)
  refine ⟨ε_0, C, hε_0_pos, hC_pos, ?_⟩
  intro ε hε_pos hε_lt_ε_0 hε_lt_max hwbar_init hode
  -- Step 5: under JEPA hyps AND ε < ε_max, t_aux ε = t_crit Wbar ε, so the
  -- formula in t_aux equals the formula in t_crit Wbar. Apply hbound and
  -- rewrite.
  have hwindow : JEPAwindow ε ∧ ε < ε_max := ⟨⟨hwbar_init, hode⟩, hε_lt_max⟩
  have h_eq : t_aux ε = t_crit Wbar ε := by simp [t_aux, if_pos hwindow]
  have := hbound ε hε_pos hε_lt_ε_0
  -- hbound: |((L / (lam * t_aux ε * ε^{1/L}))^{1/(2L-2)}) − ρ| ≤ C·ε^{1/L}·|log ε|
  -- Goal:   |((L / (lam * t_crit Wbar ε * ε^{1/L}))^{1/(2L-2)}) − ρ| ≤ same
  simp only [h_eq] at this
  exact this

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
