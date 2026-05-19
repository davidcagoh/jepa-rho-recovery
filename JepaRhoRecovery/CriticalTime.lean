/-
# JepaRhoRecovery.CriticalTime

Hand-port of paper-1's critical-time machinery (`hittingTime`,
`bernoulli_laurent_bound`, `actual_critical_time`) adapted to the
**signed eigenbasis** of the spinoff.

Per the spinoff's architecture invariant (see `CLAUDE.md`), we re-derive
the paper-1 lineage locally rather than Lake-depending on
`jepa-learning-order`. This isolates the spinoff from paper-1's evolving
build graph and lets us use `SignedGenEigenbasis` (with explicit
positivity hypothesis at the call site) in place of paper-1's
`GenEigenbasis` (which bakes `0 < ρ` into the type).

## Lineage

Source: `jepa-learning-order/JepaLearningOrder/JEPA.lean`
  * `hittingTime` (line 474) — copied verbatim, purely structural.
  * `bernoulli_laurent_bound` (line 741, Aristotle-status: 2 internal
    *named sorries* per paper-1's CompCert-convention elision —
    `h_gronwall` = Picard-Lindelöf + ODE comparison sandwich;
    `h_laurent` = Littwin 2024 Thm 4.5 applied to the exact Bernoulli ODE).
    Faithfully ported with the same two named sorries; no new
    mathematical debt.
  * `actual_critical_time_signed` (paper-1 `actual_critical_time`,
    line 848) — adapted to `SignedGenEigenbasis` with explicit
    `hrho_pos : 0 < (eb.pairs r).rho`. Sorry-free given the above two.

## What this unlocks

  * `Inversion.rho_hat_rate` (Layer 2.2, already sorry-free) takes an
    abstract `t_crit` + `h_laurent` Laurent-expansion hypothesis. The
    `actual_critical_time_signed` lemma here is the canonical *provider*
    for that hypothesis under JEPA data — closes the loop from JEPA
    trajectory to ρ̂ recovery without parametrising over abstract inputs.
  * Future Layer 3.2 (`finite_sample_rate_pos`) likely consumes a
    sample-side variant of this; having the structure in place locally
    avoids cross-repo coupling.

## Out of scope

  * No attempt to discharge the two named sorries — that requires
    Picard-Lindelöf existence + Grönwall sandwich infrastructure
    (`h_gronwall`) and the full Littwin Thm 4.5 derivation (`h_laurent`).
    These are exactly the elided steps paper-1 carries.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real
open scoped Matrix

namespace JepaRhoRecovery

/-! ## Hitting time -/

/-- **Hitting time of a continuous process at threshold `θ`.**
    First time at which `f t ≥ θ`. Defined as the infimum over the set
    `{t ∈ Set.Icc 0 t_max | f t ≥ θ}`; if the set is empty, defaults to
    `t_max + 1` (an unattainable sentinel).

    Copied from paper-1 `jepa-learning-order` `JEPA.lean:474`. -/
noncomputable def hittingTime (f : ℝ → ℝ) (θ : ℝ) (t_max : ℝ) : ℝ :=
  sInf ({t ∈ Set.Icc (0 : ℝ) t_max | f t ≥ θ} ∪ {t_max + 1})

/-! ## Bernoulli ODE Laurent bound (scalar form) -/

/-- **`bernoulli_laurent_bound` (scalar, positive branch).**

    For the perturbed Bernoulli ODE
        `σ̇(t) = λ · σ(t)^{3 − 1/L} · (1 − σ(t)^{1/L} / ρ) + R(t)`
    with `|R(t)| ≤ C · ε^{(2L−1)/L}` and `σ(0) = ε`, the hitting time
    `τ = inf {t | σ(t) ≥ p · ρ^L}` satisfies the Laurent expansion
        `|τ − (1/λ) · ∑_{n=1}^{2L−1} L / (n · ρ^{2L−n−1} · ε^{n/L})|
           ≤ K · ε^{−(L−2)/L}`.

    The proof, faithfully transplanted from paper-1, decomposes into:

      * `h_gronwall` — Picard-Lindelöf existence for the exact
        Bernoulli ODE + ODE-comparison Grönwall sandwich bounding the
        perturbed solution's hitting time against the exact one.
      * `h_laurent` — closed-form Laurent series for the exact
        Bernoulli ODE hitting time, via Littwin 2024 Thm 4.5
        (partial-fraction integration of `1/(ψ^{2L}(1 − ψ))`).

    Both are paper-1's *named sorries*, ported verbatim. They are the
    elided technical core; treating them as named axioms is
    CompCert-style honesty. -/
lemma bernoulli_laurent_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (C_ode : ℝ) (hC : 0 < C_ode) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    ∀ (f : ℝ → ℝ),
      f 0 = epsilon →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv f t - ((L : ℝ) * lam
              * Real.rpow (f t) (3 - 1 / L)
              * (1 - Real.rpow (f t) (1 / L) / rho))|
        ≤ C_ode * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
      |hittingTime f (p * rho ^ L) t_max
         - (1 / lam)
           * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
               (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                           * epsilon ^ ((n : ℝ) / L))|
        ≤ K * epsilon ^ (-((L : ℝ) - 2) / L) := by
  -- Step 1: Picard-Lindelöf existence + Grönwall comparison sandwich.
  -- Construct the exact Bernoulli ODE solution `f₀` with `f₀(0) = ε`,
  -- then bound `|τ_f − τ_{f₀}|` via Grönwall on `|f − f₀|`. `K₁` is
  -- proportional to `C_ode` and depends on the Lipschitz constant on
  -- a compact interval and the minimum speed near the threshold.
  -- (Named sorry — same elision as paper-1.)
  have h_gronwall : ∃ K₁ : ℝ, 0 < K₁ ∧
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
      ∀ (f : ℝ → ℝ),
        f 0 = epsilon →
        (∀ t ∈ Set.Ioo 0 t_max,
          |deriv f t - ((L : ℝ) * lam
                * Real.rpow (f t) (3 - 1 / (L : ℝ))
                * (1 - Real.rpow (f t) (1 / (L : ℝ)) / rho))|
          ≤ C_ode * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) →
        ∃ (f₀ : ℝ → ℝ),
          f₀ 0 = epsilon ∧
          (∀ t ∈ Set.Ioo 0 t_max,
            deriv f₀ t = (L : ℝ) * lam
                  * Real.rpow (f₀ t) (3 - 1 / (L : ℝ))
                  * (1 - Real.rpow (f₀ t) (1 / (L : ℝ)) / rho)) ∧
          |hittingTime f (p * rho ^ L) t_max
             - hittingTime f₀ (p * rho ^ L) t_max|
            ≤ K₁ * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)) := by
    sorry -- Picard-Lindelöf + Grönwall sandwich (paper-1 named sorry).
  -- Step 2: Laurent bound for the exact Bernoulli ODE (Littwin Thm 4.5).
  -- (Named sorry — same elision as paper-1.)
  have h_laurent : ∃ K₂ : ℝ, 0 < K₂ ∧
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
      ∀ (f₀ : ℝ → ℝ),
        f₀ 0 = epsilon →
        (∀ t ∈ Set.Ioo 0 t_max,
          deriv f₀ t = (L : ℝ) * lam
                * Real.rpow (f₀ t) (3 - 1 / (L : ℝ))
                * (1 - Real.rpow (f₀ t) (1 / (L : ℝ)) / rho)) →
        |hittingTime f₀ (p * rho ^ L) t_max
           - (1 / lam)
             * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
                 (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                               * epsilon ^ ((n : ℝ) / (L : ℝ)))|
          ≤ K₂ * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) := by
    sorry  -- Littwin 2024 Thm 4.5 (paper-1 named sorry).
  -- Step 3: Triangle inequality + exponent comparison.
  obtain ⟨K₁, hK₁_pos, hK₁_bound⟩ := h_gronwall
  obtain ⟨K₂, hK₂_pos, hK₂_bound⟩ := h_laurent
  refine ⟨K₁ + K₂, by positivity, ?_⟩
  intro epsilon heps heps_lt f hf0 hode
  obtain ⟨f₀, hf₀_init, hf₀_ode, h_gronwall_bd⟩ :=
    hK₁_bound epsilon heps heps_lt f hf0 hode
  have h_laurent_bd :=
    hK₂_bound epsilon heps heps_lt f₀ hf₀_init hf₀_ode
  set S := (1 / lam) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
      (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1) * epsilon ^ ((n : ℝ) / (L : ℝ)))
    with hS_def
  set τ_f := hittingTime f (p * rho ^ L) t_max with hτ_f_def
  set τ_f₀ := hittingTime f₀ (p * rho ^ L) t_max with hτ_f₀_def
  have h_tri : |τ_f - S| ≤ |τ_f - τ_f₀| + |τ_f₀ - S| := by
    have : τ_f - S = (τ_f - τ_f₀) + (τ_f₀ - S) := by ring
    rw [this]; exact abs_add_le _ _
  have h_exp_le : epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)) ≤
      epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge heps heps_lt.le
    rw [div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (by omega))]
    have : (2 : ℝ) ≤ (L : ℝ) := Nat.ofNat_le_cast.mpr hL
    linarith
  calc |τ_f - S|
      ≤ |τ_f - τ_f₀| + |τ_f₀ - S| := h_tri
    _ ≤ K₁ * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)) +
        K₂ * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) :=
        add_le_add h_gronwall_bd h_laurent_bd
    _ ≤ K₁ * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) +
        K₂ * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) := by
        linarith [mul_le_mul_of_nonneg_left h_exp_le hK₁_pos.le]
    _ = (K₁ + K₂) * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ)) := by ring

/-! ## Critical time on JEPA data (signed-eigenbasis form) -/

/-- **`actual_critical_time_signed` (positive-branch only).**

    Wraps `bernoulli_laurent_bound` for the JEPA diagonal amplitude
    `σ_r(t) = ⟨u_r*, Wbar(t) v_r*⟩` under the perturbed ODE produced by
    `generalised_diagonal_ODE` (Layer 2.1, dispatched as Aristotle
    `b1361a00`).

    Hypotheses mirror paper-1 `actual_critical_time` but use
    `SignedGenEigenbasis`; positivity of `ρ` is taken as an explicit
    hypothesis (`hrho_pos`) per the spinoff's signed-first discipline.

    The signed-eigenbasis `projectedCovariance` is `μ · ρ` (defined in
    `Basic.lean`); we therefore require `0 < (eb.pairs r).rho` so that
    `0 < projectedCovariance dat eb r`. -/
lemma actual_critical_time_signed
    {d : ℕ}
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (r : Fin d)
    (hrho_pos : 0 < (eb.pairs r).rho)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    ∀ (Wbar : ℝ → Matrix (Fin d) (Fin d) ℝ),
      diagAmplitude dat eb (Wbar 0) r = epsilon →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
         - ((L : ℝ) * projectedCovariance dat eb r
              * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
              * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L)
                     / (eb.pairs r).rho))|
        ≤ C * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
      |hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                    (p * (eb.pairs r).rho ^ L) t_max
         - (1 / projectedCovariance dat eb r)
           * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
               (L : ℝ) / ((n : ℝ) * (eb.pairs r).rho ^ (2 * L - n - 1)
                           * epsilon ^ ((n : ℝ) / L))|
        ≤ K * epsilon ^ (-((L : ℝ) - 2) / L) := by
  have hlam_pos : 0 < projectedCovariance dat eb r := by
    unfold projectedCovariance
    exact mul_pos hrho_pos (eb.pairs r).hmu_pos
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    bernoulli_laurent_bound L hL
      (projectedCovariance dat eb r) ((eb.pairs r).rho)
      hlam_pos hrho_pos
      p hp hp_lt t_max ht_max C hC
  exact ⟨K, hK_pos, fun epsilon heps heps_lt Wbar hwbar_init hode =>
    hK_bound epsilon heps heps_lt
      (fun t => diagAmplitude dat eb (Wbar t) r)
      hwbar_init hode⟩

end JepaRhoRecovery
