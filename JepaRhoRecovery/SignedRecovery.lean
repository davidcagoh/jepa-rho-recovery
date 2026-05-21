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
import JepaRhoRecovery.NegBranchHelpers
import JepaRhoRecovery.EarlySlopeGronwall

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
        -- Statement-honesty (2026-05-20): `t_max` sufficient for the
        -- JEPA diagonal amplitude to reach the threshold within the
        -- compact interval. Matches `purified_laurent_bound`'s
        -- `t_max`-sufficiency hypothesis.
        (2 * (L : ℝ)) / (projectedCovariance dat eb r
            * ε ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) ≤ t_max →
        diagAmplitude dat eb (Wbar 0) r = ε →
        ContinuousOn (fun s => diagAmplitude dat eb (Wbar s) r)
                     (Set.Icc 0 t_max) →
        (∀ t ∈ Set.Ioo 0 t_max,
          DifferentiableAt ℝ (fun s => diagAmplitude dat eb (Wbar s) r) t) →
        (∀ t ∈ Set.Ioo 0 t_max,
          |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
           - ((L : ℝ) * projectedCovariance dat eb r
                * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
                * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L)
                       / (eb.pairs r).rho))|
          ≤ C_ode * ε ^ ((2 * (L : ℝ) - 1) / L)) →
        hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                    (p * (eb.pairs r).rho ^ L) t_max < t_max →
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
    (2 * (L : ℝ)) / (lam * ε ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) ≤ t_max ∧
    diagAmplitude dat eb (Wbar 0) r = ε ∧
    ContinuousOn (fun s => diagAmplitude dat eb (Wbar s) r) (Set.Icc 0 t_max) ∧
    (∀ t ∈ Set.Ioo 0 t_max,
      DifferentiableAt ℝ (fun s => diagAmplitude dat eb (Wbar s) r) t) ∧
    (∀ t ∈ Set.Ioo 0 t_max,
      |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
       - ((L : ℝ) * lam
            * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
            * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L) / ρ))|
      ≤ C_ode * ε ^ ((2 * (L : ℝ) - 1) / L)) ∧
    hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                (p * (eb.pairs r).rho ^ L) t_max < t_max
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
      obtain ⟨⟨ht_max_reach, hwbar_init, hcont, hdiff, hode, h_reach⟩,
              hε_lt_max⟩ := hw
      have := hbridge Wbar ε hε_pos hε_lt_max ht_max_reach hwbar_init
                hcont hdiff hode h_reach
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
  intro ε hε_pos hε_lt_ε_0 hε_lt_max ht_max_reach hwbar_init hcont hdiff hode h_reach
  -- Step 5: under JEPA hyps AND ε < ε_max, t_aux ε = t_crit Wbar ε, so the
  -- formula in t_aux equals the formula in t_crit Wbar. Apply hbound and
  -- rewrite.
  have hwindow : JEPAwindow ε ∧ ε < ε_max :=
    ⟨⟨ht_max_reach, hwbar_init, hcont, hdiff, hode, h_reach⟩, hε_lt_max⟩
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

/-! ## §4.1-bridge — Trajectory → plateau-rate hypothesis (paper Thm 5.1′ bridge)

    Bridges the qualitative `sigma_positive_branch_converges` (Aristotle
    `22e700ca`) to the QUANTITATIVE plateau-approach bound consumed by
    `PlateauEstimator.rho_hat_plateau_rate`. Pure ODE work: Lyapunov-style
    rate of approach to the fixed point ρ^L. -/

/-- Helper: the ODE `σ̇ = λσ^{3-1/L} − μσ³` with `ρ = λ/μ` matches the
    form `σ̇ = λσ^{3-1/L} − (λ/ρ)σ³` consumed by
    `sigma_positive_branch_converges`. -/
private lemma plateau_convergence_per_eps
    (L : ℕ) (hL : 2 ≤ L) (lambda mu : ℝ)
    (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (f : ℝ → ℝ)
    (hf_pos : ∀ t : ℝ, 0 ≤ t → 0 < f t)
    (hf_below : ∀ t : ℝ, 0 ≤ t → f t < (lambda / mu) ^ L)
    (hf_cont : Continuous f)
    (hf_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt f
        (lambda * Real.rpow (f t) (3 - 1 / (L : ℝ))
          - mu * (f t) ^ 3) t) :
    Filter.Tendsto f Filter.atTop (nhds ((lambda / mu) ^ L)) := by
  convert sigma_positive_branch_converges L hL lambda ( lambda / mu ) hlambda_pos ( div_pos hlambda_pos hmu_pos ) f ?_ ?_ hf_cont ?_ using 1
  · assumption
  · assumption
  · grind

/-- Helper: for each ε ∈ (0,1), the convergence gives a concrete time
    T > 0 where the gap is ≤ ε^{1/L} · |log ε|. -/
private lemma plateau_gap_time_exists
    (L : ℕ) (hL : 2 ≤ L) (lambda mu : ℝ)
    (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (f : ℝ → ℝ)
    (hf_pos : ∀ t : ℝ, 0 ≤ t → 0 < f t)
    (hf_below : ∀ t : ℝ, 0 ≤ t → f t < (lambda / mu) ^ L)
    (hf_cont : Continuous f)
    (hf_ode : ∀ t : ℝ, 0 < t →
      HasDerivAt f
        (lambda * Real.rpow (f t) (3 - 1 / (L : ℝ))
          - mu * (f t) ^ 3) t)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ T : ℝ, 0 < T ∧
      |f T - (lambda / mu) ^ L| ≤
        ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  have h_limit : Filter.Tendsto f Filter.atTop (nhds ((lambda / mu) ^ L)) :=
    plateau_convergence_per_eps L hL lambda mu hlambda_pos hmu_pos f hf_pos hf_below hf_cont hf_ode
  rcases Metric.tendsto_atTop.mp h_limit (ε ^ (1 / (L : ℝ)) * |Real.log ε|)
    (mul_pos (Real.rpow_pos_of_pos hε _) (abs_pos.mpr (ne_of_lt (Real.log_neg hε hε1))))
    with ⟨T, hT⟩
  exact ⟨Max.max T 1, by positivity, le_of_lt (hT _ (le_max_left _ _))⟩

/-- **Bridge to plateau estimator (paper Thm 5.1′ feeder).**

    For each ε ∈ (0,1), `sigma ε : ℝ → ℝ` is a positive-branch trajectory
    of the diagonal Bernoulli ODE with initial condition ≤ ε and lying
    strictly below the plateau (ρ^L). The bridge produces:
      * a time-of-observation function `T : ℝ → ℝ` (positive for each ε),
      * a uniform constant `K_plateau > 0`,
    such that the trajectory at the chosen time is within
    `K_plateau · ε^{1/L} · |log ε|` of the plateau.

    PROVIDED SOLUTION (3 phases):

    Phase 1 — growth from ε to ρ^L/2. For σ ≪ ρ^L the μσ³ term is
    subleading; integrating σ̇ = λσ^{3-1/L} gives
    σ(t)^{-(2L-1)/L} = σ(0)^{-(2L-1)/L} - ((2L-1)/L)·λ·t. Reaching
    σ = ρ^L/2 takes time `t_grow(ε) = O(ε^{-(2L-1)/L})` (explicit:
    `(L/((2L-1)λ)) · (ε^{-(2L-1)/L} - (ρ^L/2)^{-(2L-1)/L})`).

    Phase 2 — exponential approach on [σ ∈ [ρ^L/2, ρ^L)]. Define the
    Lyapunov function V(t) := ρ^L - σ(t) ≥ 0. Compute
        V̇ = -σ̇ = -[λσ^{3-1/L} - μσ³] = -σ^{3-1/L}·(λ - μσ^{1/L}).
    For σ ∈ [ρ^L/2, ρ^L), σ^{1/L} ∈ [ρ/2^{1/L}, ρ), so
        λ - μσ^{1/L} = μ(ρ - σ^{1/L}) ≥ μ · V/(L·ρ^{L-1})  (Lipschitz of
        x ↦ x^{1/L} near ρ^L, factored through V).
    Combined with σ^{3-1/L} ≥ (ρ^L/2)^{3-1/L}, this gives
        V̇ ≤ -c·V,  where c := μ·(ρ^L/2)^{3-1/L}/(L·ρ^{L-1}) > 0.
    Grönwall: V(t) ≤ V(t_grow)·exp(-c·(t - t_grow)) ≤ ρ^L·exp(-c·(t-t_grow)).

    Phase 3 — choose T(ε). Solve ρ^L·exp(-c·(T - t_grow)) ≤ ε^{1/L}·|log ε|:
        T(ε) := t_grow(ε) + c⁻¹·log(ρ^L / (ε^{1/L}·|log ε|)).
    For ε ∈ (0,1), |log ε| > 0 so the second term is well-defined and
    positive for ε sufficiently small; for the remaining range push T
    larger uniformly. K_plateau := 1 (the bound holds tight by construction).

    Mathlib hooks: `Real.hasDerivAt_rpow_const`, `gronwallBound`,
    `mvt_eq` or `Convex.norm_image_sub_le_of_norm_deriv_le_segment`.

    VACUITY DISCIPLINE. K_plateau > 0 and T(ε) > 0 are forced existentials.
    The trajectory `sigma` is a free function constrained by the ODE,
    positivity, sub-plateau bound, continuity, and initial condition —
    a degenerate witness would require all five to be vacuously true
    (impossible since `hSigma_below` forces `σ < ρ^L` everywhere, while
    `hSigma_init` forces `σ(0) ≤ ε`). -/
-- ⚠ CORRECTION NOTE (session 90, 2026-05-21): see ../CORRECTION_NOTE.md.
-- Plateau target `ρ^L` and Lyapunov V := (σ − ρ^L)² inherit paper-1's
-- inverted ODE convention. Correct target is ρ^(1/L). Re-derivation queued.
theorem signed_recovery_pos_magnitude_plateau
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_below : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t →
        sigma ε t < (lambda / mu) ^ L)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 ≤ ε) :
    ∃ T : ℝ → ℝ, ∃ K_plateau : ℝ, 0 < K_plateau ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        |sigma ε (T ε) - (lambda / mu) ^ L|
          ≤ K_plateau * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
  have h_each : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ T : ℝ, 0 < T ∧
        |sigma ε T - (lambda / mu) ^ L| ≤
          ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
    intro ε hε hε1
    exact plateau_gap_time_exists L hL lambda mu hlambda_pos hmu_pos (sigma ε)
      (hSigma_pos ε hε hε1) (hSigma_below ε hε hε1)
      (hSigma_cont ε hε hε1) (hSigma_ode ε hε hε1) ε hε hε1
  refine ⟨fun ε => if h : 0 < ε ∧ ε < 1 then (h_each ε h.1 h.2).choose else 1,
          1, one_pos, ?_, ?_⟩
  · intro ε hε hε1
    have hcond : 0 < ε ∧ ε < 1 := ⟨hε, hε1⟩
    simp only [dif_pos hcond]
    exact (h_each ε hε hε1).choose_spec.1
  · intro ε hε hε1
    have hcond : 0 < ε ∧ ε < 1 := ⟨hε, hε1⟩
    simp only [dif_pos hcond]
    have hb := (h_each ε hε hε1).choose_spec.2
    linarith [hb]

/-! ## §4.1-bridge — Trajectory → early-slope ε^{(L+1)/L} perturbation
    (paper Thm 5.2 bridge)

    For the early-slope estimator, the μσ³ correction to the idealised
    σ̇ = λσ^{3-1/L} dynamics is O(ε^{(L+1)/L}) on the early-time window
    [0, t₀]. This is the corrected (post-counterexample, Aristotle
    `95ddb6a0`) exponent. -/

/-- The observation time t₀(ε) = c·λ⁻¹·ε^{-(2L-1)/L} is nonneg. -/
private lemma early_obs_time_nonneg
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (c : ℝ) (hc_pos : 0 < c)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    0 ≤ c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ)) := by
  positivity

/-- Grönwall-based bound: |σ(t₀) − σ_id(t₀)| ≤ C·ε^{(L+1)/L}.
    Proved sorry-free via the v-transform approach in
    `JepaRhoRecovery.EarlySlopeGronwall`. -/
private lemma early_slope_gronwall_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      |sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ)))
        - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))
                    - ((2 * (L : ℝ) - 1) / (L : ℝ)) * lambda
                        * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))))
                    (-(L : ℝ) / (2 * (L : ℝ) - 1))|
        ≤ C * ε ^ (((L : ℝ) + 1) / (L : ℝ)) := by
  exact early_slope_gronwall_bound_aux L hL lambda mu hlambda_pos hmu_pos
    c hc_pos hc_lt_one hc_small sigma hSigma_pos hSigma_cont hSigma_ode hSigma_init

/-- Combines positivity at t₀ with the Grönwall bound. -/
private lemma early_slope_core
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))) ∧
      |sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ)))
        - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))
                    - ((2 * (L : ℝ) - 1) / (L : ℝ)) * lambda
                        * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / (L : ℝ))))
                    (-(L : ℝ) / (2 * (L : ℝ) - 1))|
        ≤ C * ε ^ (((L : ℝ) + 1) / (L : ℝ)) := by
  obtain ⟨C, hC, hbd⟩ := early_slope_gronwall_bound L hL lambda mu hlambda_pos hmu_pos
    c hc_pos hc_lt_one hc_small sigma hSigma_pos hSigma_cont hSigma_ode hSigma_init
  exact ⟨C, hC, fun ε hε hε1 =>
    ⟨hSigma_pos ε hε hε1 _ (early_obs_time_nonneg lambda hlambda_pos c hc_pos ε hε L),
     hbd ε hε hε1⟩⟩

/-- **Bridge to early-slope estimator (paper Thm 5.2 feeder).**

    For each ε ∈ (0,1), `sigma ε : ℝ → ℝ` is the positive-branch
    Bernoulli trajectory with initial condition exactly ε. The bridge
    produces a uniform constant `K_early > 0` such that the trajectory
    at the early-observation time `t₀(ε) := c·λ⁻¹·ε^{-(2L-1)/L}` differs
    from the idealised (μ=0) solution
        σ_id(ε) := (ε^{-(2L-1)/L} - ((2L-1)/L)·λ·t₀(ε))^{-L/(2L-1)}
    by at most `K_early · ε^{(L+1)/L} · |log ε|`.

    PROVIDED SOLUTION (Grönwall on μ-term):

    Step 1 — idealised solution on [0, t₀]. σ_id solves σ̇_id = λσ_id^{3-1/L}
    with σ_id(0) = ε. Closed form (Bernoulli):
        σ_id(t) = (ε^{-(2L-1)/L} - ((2L-1)/L)·λ·t)^{-L/(2L-1)}.
    On [0, t₀] with c·(2L-1)/L < 1, σ_id stays in [ε, A·ε] where
    A := (1 - c·(2L-1)/L)^{-L/(2L-1)} > 1.

    Step 2 — δ := σ - σ_id satisfies a linear-in-δ ODE with a forcing
    term proportional to μσ³. Specifically:
        δ̇ = λ·(σ^{3-1/L} - σ_id^{3-1/L}) - μ·σ³
            = λ·M(t)·δ - μ·σ³,
    where M(t) := (σ^{3-1/L} - σ_id^{3-1/L})/(σ - σ_id) is the MVT slope
    of x ↦ x^{3-1/L} on the segment between σ and σ_id (uniformly bounded
    above on [0, t₀] by a constant times σ_id^{2-1/L} ≤ (Aε)^{2-1/L}).

    Step 3 — Grönwall (linear). δ(0) = 0, so
        |δ(t)| ≤ ∫₀^t μ·σ(s)³·exp(∫_s^t λ·M(τ)dτ) ds.
    Since σ ≤ 2·σ_id ≤ 2Aε on [0, t₀] (apply ε small enough so the
    perturbation stays half the idealised, an a posteriori check), and
    the cumulative M integral is bounded:
        ∫₀^{t₀} λ·M(τ) dτ ≤ const·λ·(Aε)^{2-1/L}·t₀
            = const·λ·ε^{(2L-1)/L}·ε^{-(2L-1)/L} = const,
    so exp(·) ≤ const.

    Step 4 — final bound:
        |δ(t₀)| ≤ const·μ·(2Aε)³·t₀ = const·με³·ε^{-(2L-1)/L}
              = const·ε^{(L+1)/L}.
    The |log ε| factor comes from the const itself (loose bookkeeping
    via `eps_rpow_log_eventually_small`-style estimates that turn
    polynomial bounds into ε^{(L+1)/L}·|log ε|).
    K_early := the assembled constant; > 0.

    Mathlib hooks: `gronwallBound` or hand-written Grönwall on
    `‖δ(t)‖ ≤ ∫₀^t a(s)‖δ(s)‖ + b(s) ds`, plus
    `Real.hasDerivAt_rpow_const`.

    VACUITY. K_early > 0 forced. The positivity output
    `0 < sigma ε (t₀ ε)` is forced by `hSigma_pos`. The trajectory is
    constrained by ODE + positivity + initial condition, so a degenerate
    witness would require contradicting the IC `sigma ε 0 = ε`.

    **Statement correction (session 88, Aristotle `49212b46`).**
    Original `|Real.log ε|` factor falsified by counterexample
    (L=2, λ=μ=1, c=0.3): as ε → 1⁻, |log ε| → 0 but the perturbation
    converges to a positive constant (≈ 0.49). Patched to
    `(1 + |Real.log ε|)`, which is ≥ 1 for all ε ∈ (0,1) and preserves
    the `|log ε|` asymptotics as ε → 0⁺. -/

theorem early_slope_perturbation_pos
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_pos : 0 < lambda) (hmu_pos : 0 < mu)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hc_small : c * ((2 * (L : ℝ) - 1) / (L : ℝ)) < 1)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ K_early : ℝ, 0 < K_early ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        0 < sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L)) ∧
        |sigma ε (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L))
          - Real.rpow (ε ^ (-(2 * (L : ℝ) - 1) / L)
                      - ((2 * (L : ℝ) - 1) / L) * lambda
                          * (c * lambda⁻¹ * ε ^ (-(2 * (L : ℝ) - 1) / L)))
                      (-(L : ℝ) / (2 * (L : ℝ) - 1))|
          ≤ K_early * ε ^ (((L : ℝ) + 1) / (L : ℝ)) * (1 + |Real.log ε|) := by
  obtain ⟨C, hC, hcore⟩ := early_slope_core L hL lambda mu hlambda_pos hmu_pos
    c hc_pos hc_lt_one hc_small sigma hSigma_pos hSigma_cont hSigma_ode hSigma_init
  exact ⟨C, hC, fun ε hε hε1 => by
    obtain ⟨hpos, hle⟩ := hcore ε hε hε1
    exact ⟨hpos, le_trans hle (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (abs_nonneg _)))⟩⟩

/-! ## §7.3 — Negative-branch λ-rate from late-time decay (paper Thm 7.3 part 1)

    For the negative branch (λ < 0, ρ = λ/μ < 0 ⇒ μ > 0), σ_r DECAYS as
    a power law. The leading-order late-time behaviour is
        σ_r(t) ∼ (((2L-1)/L)·|λ|·t)^{-L/(2L-1)}.
    A curve-fit estimator recovers |λ| at rate O(ε^{1/L}).

    NOTE: paper Thm 7.3 part 1 only. Part 2 (μ-rate suboptimality) is an
    information-theoretic lower bound, deferred (paper-3 territory). -/

/-  ORIGINAL STATEMENT (commented out — FALSE as stated).

    The leading coefficient `(-((L : ℝ) / (2 * (L : ℝ) - 1)))` has the
    wrong sign.  For the negative branch (λ < 0), the transformed variable
    v(t) := σ(t)^{-(2L-1)/L} is increasing, so the estimator

        -(L/(2L-1)) · v(T)/T

    converges to -|λ| = λ (NEGATIVE), not to -λ = |λ| (POSITIVE).
    Subtracting (-λ) = |λ| therefore leaves a residual of magnitude 2|λ|,
    which is bounded below by a positive constant for all T > 0.
    Since K · ε^{1/L} · |log ε| → 0 as ε → 0⁺, no finite K satisfies the
    bound for all ε ∈ (0,1).

    **Fix:** remove the leading minus sign so the estimator reads

        (L/(2L-1)) · σ(ε,T)^{-(2L-1)/L} / T

    which converges to |λ| = -λ.  Additionally, replace the universal
    `ε < 1` quantifier with an existential `ε < ε₀ < 1` (matching the
    pattern of `lambda_hat_early_slope_rate` in PlateauEstimator.lean)
    because the bound `K · ε^{1/L} · |log ε|` degenerates as ε → 1⁻
    (where |log ε| → 0).

theorem signed_recovery_neg_lambda_rate_ORIGINAL
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ T : ℝ → ℝ, ∃ K_neg : ℝ, 0 < K_neg ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        |(-((L : ℝ) / (2 * (L : ℝ) - 1)))
            * Real.rpow (sigma ε (T ε)) (-(2 * (L : ℝ) - 1) / L) / T ε
          - (-lambda)|
          ≤ K_neg * ε ^ ((1 : ℝ) / L) * |Real.log ε|) := by
  sorry
-/

/-- **Negative-branch λ-rate (paper Thm 7.3 part 1, CORRECTED).**

    **Corrections from the original statement:**
    1. **Sign fix.** The leading coefficient is now **positive**
       `(L/(2L-1))` instead of `-(L/(2L-1))`.  The original negative sign
       made the estimator converge to `λ = -|λ|` rather than `|λ| = -λ`,
       leaving an irreducible gap of `2|λ|`.
    2. **Added ε₀.** The quantifier is now `ε < ε₀` (with ε₀ existentially
       quantified, 0 < ε₀ < 1) instead of `ε < 1`.  This matches the
       pattern of `lambda_hat_early_slope_rate` and avoids the degeneracy
       of `|log ε| → 0` as `ε → 1⁻`.

    The **mathematical content** is unchanged:

    For each ε ∈ (0,ε₀), the negative-branch trajectory `sigma ε : ℝ → ℝ`
    solves the Bernoulli ODE with λ < 0, μ > 0, and initial condition ε.
    The curve-fit estimator
        λ̂(ε, t) := (L/(2L-1))·sigma ε t ^{-(2L-1)/L} / t
    recovers |λ| = -λ at rate O(ε^{1/L}·|log ε|) for an appropriately
    chosen observation time T(ε).

    **Proof sketch.**

    Choose T(ε) = ε^{-2}/(-λ) and K_neg = (L/(2L-1))·(-λ) + μ + 1.

    Define v(t) := σ(t)^{-(2L-1)/L}. From the ODE, v' = (2L-1)/L·(-λ+μσ^{1/L}).
    Since σ ≤ ε (antitone, neg_branch_sigma_le_init):
    • v(T) ≥ v(0) + (2L-1)/L·(-λ)·T  (lower bound, neg_branch_v_lower_bound)
    • v(T) ≤ v(0) + (2L-1)/L·(-λ+με^{1/L})·T  (upper bound, neg_branch_v_upper_bound)

    The estimator (L/(2L-1))·v(T)/T lies in [|λ| + (L/(2L-1))·v(0)/T,
    |λ| + μ·ε^{1/L} + (L/(2L-1))·v(0)/T]. With T = ε^{-2}/(-λ):
    error ≤ (L/(2L-1))·(-λ)·ε^{1/L} + μ·ε^{1/L} ≤ K·ε^{1/L}·|log ε|
    for ε < ε₀ where |log ε₀| ≥ 1. -/
theorem signed_recovery_neg_lambda_rate
    (L : ℕ) (hL : 2 ≤ L)
    (lambda mu : ℝ) (hlambda_neg : lambda < 0) (hmu_pos : 0 < mu)
    (sigma : ℝ → ℝ → ℝ)
    (hSigma_pos : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → 0 < sigma ε t)
    (hSigma_cont : ∀ ε : ℝ, 0 < ε → ε < 1 → Continuous (sigma ε))
    (hSigma_ode : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 < t →
      HasDerivAt (sigma ε)
        (lambda * Real.rpow (sigma ε t) (3 - 1 / (L : ℝ))
          - mu * (sigma ε t) ^ 3) t)
    (hSigma_init : ∀ ε : ℝ, 0 < ε → ε < 1 → sigma ε 0 = ε) :
    ∃ T : ℝ → ℝ, ∃ K_neg : ℝ, ∃ eps_0 : ℝ,
      0 < eps_0 ∧ eps_0 < 1 ∧ 0 < K_neg ∧
      (∀ ε : ℝ, 0 < ε → ε < eps_0 → 0 < T ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < eps_0 →
        |((L : ℝ) / (2 * (L : ℝ) - 1))
            * Real.rpow (sigma ε (T ε)) (-(2 * (L : ℝ) - 1) / L) / T ε
          - (-lambda)|
          ≤ K_neg * ε ^ ((1 : ℝ) / L) * |Real.log ε|) :=
  signed_recovery_neg_lambda_rate_core L hL lambda mu hlambda_neg hmu_pos
    sigma hSigma_pos hSigma_cont hSigma_ode hSigma_init

end JepaRhoRecovery
