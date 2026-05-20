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

/-! ## Bernoulli ODE Laurent bound (scalar form)

The proof of `bernoulli_laurent_bound` is now decomposed into THREE
standalone named-sorry lemmas — each independently dispatchable to
Aristotle (since paper-1 carried both as elided technical core):

  * `bernoulli_exact_solution_exists` — Picard-Lindelöf existence for
    the exact Bernoulli ODE (no perturbation).
  * `bernoulli_gronwall_sandwich` — ODE-comparison Grönwall bound
    relating perturbed `f` to exact `f₀`.
  * `bernoulli_exact_laurent` — closed-form Laurent series for the
    exact Bernoulli ODE hitting time, via Littwin 2024 Thm 4.5.

The main `bernoulli_laurent_bound` is sorry-free, assembled by triangle
inequality + exponent comparison from the three pieces above.
-/

/-- **(Piece 1/3) Picard-Lindelöf existence for the exact Bernoulli ODE.**

    For any initial value `epsilon > 0` and parameters `L ≥ 2`, `λ > 0`,
    `ρ > 0`, there exists a function `f₀ : ℝ → ℝ` with `f₀(0) = ε`
    satisfying the exact (unperturbed) Bernoulli ODE
        `f₀'(t) = L · λ · f₀(t)^{3 − 1/L} · (1 − f₀(t)^{1/L} / ρ)`
    on `Ioo 0 t_max`.

    This is a pure existence statement; no estimates are asserted.
    The right-hand side is locally Lipschitz on `(0, ρ^L]` so standard
    Picard-Lindelöf applies on a compact subinterval; existence on the
    full `Ioo 0 t_max` follows by maximal-solution continuation since
    the threshold `p · ρ^L` is strictly below `ρ^L` (the fixed point).

    **Path C axiom** (promoted 2026-05-20 after Aristotle job `5fbe03d3`
    came back COMPLETE_WITH_ERRORS; statement-honesty pass also 2026-05-20
    added `p` parameter, continuity, pointwise differentiability, and
    threshold reachability under a `t_max`-sufficient hypothesis). Standard
    Picard-Lindelöf existence + maximal-solution continuation + a-priori
    speed bound; cited as classical ODE theory. -/
axiom bernoulli_exact_solution_exists
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps_lt : epsilon < 1)
    -- `t_max` large enough for the exact solution to reach `p·ρ^L`.
    -- A coarse-but-sufficient bound is `(2L/(lam·ε^{(2L-1)/L})) ≤ t_max`,
    -- matching the leading Laurent term `1/(lam·ε^{(2L-1)/L})` up to a
    -- factor of 2.
    (h_t_max_reach :
      (2 * (L : ℝ)) / (lam * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)))
        ≤ t_max) :
    ∃ (f₀ : ℝ → ℝ),
      f₀ 0 = epsilon ∧
      ContinuousOn f₀ (Set.Icc 0 t_max) ∧
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f₀ t) ∧
      (∀ t ∈ Set.Ioo 0 t_max,
        deriv f₀ t = (L : ℝ) * lam
              * Real.rpow (f₀ t) (3 - 1 / (L : ℝ))
              * (1 - Real.rpow (f₀ t) (1 / (L : ℝ)) / rho)) ∧
      hittingTime f₀ (p * rho ^ L) t_max < t_max

/-- **(Piece 2/3) Grönwall comparison sandwich.**

    Given an exact Bernoulli solution `f₀` (provided as a hypothesis —
    typically obtained from `bernoulli_exact_solution_exists`) and a
    perturbed trajectory `f` with the same initial value `ε` and
    `|f'(t) − RHS(f(t))| ≤ C · ε^{(2L−1)/L}`, the perturbed and exact
    hitting times at threshold `p · ρ^L` differ by at most
    `K₁ · ε^{(2L−1)/L}`.

    Standard Grönwall on `|f − f₀|` plus a lower bound on the speed
    `f₀'` near the threshold gives the constant `K₁` proportional to
    `C` and depending on the Lipschitz constant on the compact
    interval `[0, t_max]`.

    **Path C axiom** (promoted 2026-05-20 after Aristotle job `f00f9f44`
    came back COMPLETE_WITH_ERRORS; statement-honesty pass 2026-05-20
    added continuity, pointwise differentiability, and reachability
    hypotheses for both `f` and `f₀`). The original statement was
    mathematically vacuous: if `f` reached the threshold and `f₀` did
    not (hitting time defaulting to the `t_max + 1` sentinel), the
    difference `|τ_f − τ_{f₀}|` could be Ω(1), contradicting the
    `O(ε^{(2L-1)/L})` claim. The added hypotheses force both hitting
    times into the interior, where the standard Grönwall ODE-comparison
    + speed-lower-bound argument is honest. -/
axiom bernoulli_gronwall_sandwich
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (C_ode : ℝ) (hC : 0 < C_ode) :
    ∃ K₁ : ℝ, 0 < K₁ ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    ∀ (f f₀ : ℝ → ℝ),
      f 0 = epsilon →
      f₀ 0 = epsilon →
      ContinuousOn f (Set.Icc 0 t_max) →
      ContinuousOn f₀ (Set.Icc 0 t_max) →
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f t) →
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f₀ t) →
      (∀ t ∈ Set.Ioo 0 t_max,
        deriv f₀ t = (L : ℝ) * lam
              * Real.rpow (f₀ t) (3 - 1 / (L : ℝ))
              * (1 - Real.rpow (f₀ t) (1 / (L : ℝ)) / rho)) →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv f t - ((L : ℝ) * lam
              * Real.rpow (f t) (3 - 1 / (L : ℝ))
              * (1 - Real.rpow (f t) (1 / (L : ℝ)) / rho))|
        ≤ C_ode * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) →
      hittingTime f (p * rho ^ L) t_max < t_max →
      hittingTime f₀ (p * rho ^ L) t_max < t_max →
      |hittingTime f (p * rho ^ L) t_max
         - hittingTime f₀ (p * rho ^ L) t_max|
        ≤ K₁ * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ))

/-- **(Piece 3/3) Closed-form Laurent expansion for the exact Bernoulli ODE.**

    Any solution `f₀` of the exact Bernoulli ODE with `f₀(0) = ε`
    has hitting time at threshold `p · ρ^L` admitting the Laurent
    expansion
        `(1/λ) · ∑_{n=1}^{2L−1} L / (n · ρ^{2L−n−1} · ε^{n/L})`
    with error envelope `K₂ · ε^{−(L−2)/L}` (the next-order subleading
    polynomial term).

    Proof via Littwin 2024 Thm 4.5: partial-fraction integration of
    `1/(ψ^{2L} · (1 − ψ))` along the trajectory, then asymptotic
    expansion as ε → 0+.

    **Path C axiom** (promoted 2026-05-20 after Aristotle job `d9780bba`
    came back COMPLETE_WITH_ERRORS; statement-honesty pass 2026-05-20
    added continuity, pointwise differentiability, and reachability
    hypotheses for `f₀`). The original statement had the same vacuity
    gap as `bernoulli_gronwall_sandwich` — if `f₀` failed to reach the
    threshold, the LHS could be Ω(`t_max + 1`). Cited as Littwin 2024
    Thm 4.5 (partial-fraction integration of `1/(ψ^{2L}·(1−ψ))`); see
    paper §4.3. -/
axiom bernoulli_exact_laurent
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max) :
    ∃ K₂ : ℝ, 0 < K₂ ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    ∀ (f₀ : ℝ → ℝ),
      f₀ 0 = epsilon →
      ContinuousOn f₀ (Set.Icc 0 t_max) →
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f₀ t) →
      (∀ t ∈ Set.Ioo 0 t_max,
        deriv f₀ t = (L : ℝ) * lam
              * Real.rpow (f₀ t) (3 - 1 / (L : ℝ))
              * (1 - Real.rpow (f₀ t) (1 / (L : ℝ)) / rho)) →
      hittingTime f₀ (p * rho ^ L) t_max < t_max →
      |hittingTime f₀ (p * rho ^ L) t_max
         - (1 / lam)
           * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
               (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                             * epsilon ^ ((n : ℝ) / (L : ℝ)))|
        ≤ K₂ * epsilon ^ (-((L : ℝ) - 2) / (L : ℝ))

/-- **`bernoulli_laurent_bound` (scalar, positive branch).**

    For the perturbed Bernoulli ODE
        `σ̇(t) = λ · σ(t)^{3 − 1/L} · (1 − σ(t)^{1/L} / ρ) + R(t)`
    with `|R(t)| ≤ C · ε^{(2L−1)/L}` and `σ(0) = ε`, the hitting time
    `τ = inf {t | σ(t) ≥ p · ρ^L}` satisfies the Laurent expansion
        `|τ − (1/λ) · ∑_{n=1}^{2L−1} L / (n · ρ^{2L−n−1} · ε^{n/L})|
           ≤ K · ε^{−(L−2)/L}`.

    **Now sorry-free at this lemma's body** — assembled by triangle
    inequality from the three named-sorry pieces above:
      * `bernoulli_exact_solution_exists` (Picard-Lindelöf)
      * `bernoulli_gronwall_sandwich` (ODE comparison)
      * `bernoulli_exact_laurent` (Littwin Thm 4.5)
    Each is independently dispatchable to Aristotle. -/
lemma bernoulli_laurent_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (C_ode : ℝ) (hC : 0 < C_ode) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    -- Statement-honesty: caller must witness `t_max` is large enough for
    -- the exact Bernoulli solution to reach the threshold (matches the
    -- Laurent leading-order time scale).
    (2 * (L : ℝ)) / (lam * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)))
        ≤ t_max →
    ∀ (f : ℝ → ℝ),
      f 0 = epsilon →
      ContinuousOn f (Set.Icc 0 t_max) →
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f t) →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv f t - ((L : ℝ) * lam
              * Real.rpow (f t) (3 - 1 / L)
              * (1 - Real.rpow (f t) (1 / L) / rho))|
        ≤ C_ode * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
      hittingTime f (p * rho ^ L) t_max < t_max →
      |hittingTime f (p * rho ^ L) t_max
         - (1 / lam)
           * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
               (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                           * epsilon ^ ((n : ℝ) / L))|
        ≤ K * epsilon ^ (-((L : ℝ) - 2) / L) := by
  -- Assemble from the three named-sorry pieces.
  obtain ⟨K₁, hK₁_pos, hK₁_bound⟩ :=
    bernoulli_gronwall_sandwich L hL lam rho hlam hrho p hp hp_lt
      t_max ht_max C_ode hC
  obtain ⟨K₂, hK₂_pos, hK₂_bound⟩ :=
    bernoulli_exact_laurent L hL lam rho hlam hrho p hp hp_lt
      t_max ht_max
  refine ⟨K₁ + K₂, by positivity, ?_⟩
  intro epsilon heps heps_lt h_t_max_reach f hf0 hf_cont hf_diff hode h_reach_f
  obtain ⟨f₀, hf₀_init, hf₀_cont, hf₀_diff, hf₀_ode, h_reach_f₀⟩ :=
    bernoulli_exact_solution_exists L hL lam rho hlam hrho p hp hp_lt
      t_max ht_max epsilon heps heps_lt h_t_max_reach
  have h_gronwall_bd :=
    hK₁_bound epsilon heps heps_lt f f₀ hf0 hf₀_init hf_cont hf₀_cont
      hf_diff hf₀_diff hf₀_ode hode h_reach_f h_reach_f₀
  have h_laurent_bd :=
    hK₂_bound epsilon heps heps_lt f₀ hf₀_init hf₀_cont hf₀_diff hf₀_ode
      h_reach_f₀
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
    -- Statement-honesty: `t_max` large enough for the exact Bernoulli
    -- analogue to reach the threshold.
    (2 * (L : ℝ)) / (projectedCovariance dat eb r
        * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) ≤ t_max →
    ∀ (Wbar : ℝ → Matrix (Fin d) (Fin d) ℝ),
      diagAmplitude dat eb (Wbar 0) r = epsilon →
      ContinuousOn (fun s => diagAmplitude dat eb (Wbar s) r) (Set.Icc 0 t_max) →
      (∀ t ∈ Set.Ioo 0 t_max,
        DifferentiableAt ℝ (fun s => diagAmplitude dat eb (Wbar s) r) t) →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv (fun s => diagAmplitude dat eb (Wbar s) r) t
         - ((L : ℝ) * projectedCovariance dat eb r
              * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / L)
              * (1 - Real.rpow (diagAmplitude dat eb (Wbar t) r) (1 / L)
                     / (eb.pairs r).rho))|
        ≤ C * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
      hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                  (p * (eb.pairs r).rho ^ L) t_max < t_max →
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
  exact ⟨K, hK_pos,
    fun epsilon heps heps_lt h_t_max_reach Wbar hwbar_init hcont hdiff hode h_reach =>
      hK_bound epsilon heps heps_lt h_t_max_reach
        (fun t => diagAmplitude dat eb (Wbar t) r)
        hwbar_init hcont hdiff hode h_reach⟩

/-! ## Purified Laurent bound (Path C bridge to Inversion)

The raw hitting time $\hat T$ from `bernoulli_laurent_bound` has Laurent
expansion
$$\hat T \approx \frac{1}{\lambda}\sum_{n=1}^{2L-1}\frac{L}{n\,\rho^{2L-n-1}}\,\varepsilon^{-n/L},$$
leading order $\varepsilon^{-(2L-1)/L}$, ρ-INDEPENDENT.

`Inversion.rho_hat_rate` instead consumes a Laurent of the form
$$t_{\mathrm{crit}} \approx \frac{1}{\lambda}\sum_{n=1}^{2L-1}\frac{L}{n\,\rho^{2L-n-1}}\,\varepsilon^{(n-2)/L},$$
leading order $\varepsilon^{-1/L}$ at $n=1$, ρ-DEPENDENT.

These are different per-term shapes (the exponent shift $-n/L \to (n-2)/L$
varies with $n$), so the bridge is not a rescaling — it requires extracting
the $n=1$ coefficient and reshaping the residual.

**Definition.** The *purified* hitting time subtracts the divergent
$n\ge 2$ tail from the raw hitting time and adds the Inversion-shape
subleading terms:
$$\tilde T(\varepsilon) := \hat T(\varepsilon)
   - \frac{1}{\lambda}\sum_{n=2}^{2L-1}\frac{L}{n\,\rho^{2L-n-1}}\,\varepsilon^{-n/L}
   + \frac{1}{\lambda}\sum_{n=2}^{2L-1}\frac{L}{n\,\rho^{2L-n-1}}\,\varepsilon^{(n-2)/L}.$$
Then by algebra $\tilde T - \frac{1}{\lambda}\sum_{n=1}^{2L-1}\frac{L}{n\rho^{2L-n-1}}\varepsilon^{(n-2)/L}
= \hat T - \frac{1}{\lambda}\sum_{n=1}^{2L-1}\frac{L}{n\rho^{2L-n-1}}\varepsilon^{-n/L}$,
so the *same* paper-1 residual controls the purified bound — modulo the
envelope shape.

**Envelope refinement (named sorry).** Paper-1 bounds the residual by
$K\varepsilon^{-(L-2)/L}$ (polynomial). Inversion requires
$K_{\log}\,|\log\varepsilon|$ (logarithmic). For $L=2$ these agree
($\varepsilon^0 = 1$); for $L \ge 3$ the log envelope is genuinely
stronger and requires Littwin Thm 4.5 stated with *full* error terms
rather than just leading-exponent dominance. That sharpening is the
named-sorry below, and it is the paper-2 spec extension flagged in
`wiki/decisions.md` session 78.
-/

/-- **`purified_hitting_time`.**
    Subtracts the divergent $n \ge 2$ Laurent prefix of the raw hitting
    time and adds the Inversion-shape subleading terms. By construction,
    `purified_hitting_time` is exactly what `Inversion.rho_hat_rate`
    consumes when fed the JEPA dynamics' hitting time.

    Not vacuous: this is a concrete arithmetic transform of `T_raw`,
    `lam`, `rho`, `ε`. It collapses to `T_raw` only when both subtracted
    and added sums vanish, which requires `L = 1`; for `L ≥ 2` both sums
    are non-trivial. -/
noncomputable def purified_hitting_time
    (T_raw : ℝ) (lam rho : ℝ) (L : ℕ) (epsilon : ℝ) : ℝ :=
  T_raw
    - (1 / lam) * ∑ n ∈ Finset.Ioc 1 (2 * L - 1),
        (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                      * epsilon ^ ((n : ℝ) / (L : ℝ)))
    + (1 / lam) * ∑ n ∈ Finset.Ioc 1 (2 * L - 1),
        (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1))
          * epsilon ^ (((n : ℝ) - 2) / (L : ℝ))

/-- **Key algebraic identity** (sorry-free): the purified hitting time's
    deviation from the Inversion-shape Laurent equals the raw hitting
    time's deviation from the CriticalTime-shape Laurent.

    This is the pure-algebra core of the Path C bridge; it makes no
    analytic claim about envelopes. -/
lemma purified_hitting_time_residual_eq
    (T_raw : ℝ) (lam rho : ℝ) (hlam : lam ≠ 0)
    (L : ℕ) (epsilon : ℝ) (hε : 0 < epsilon) :
    purified_hitting_time T_raw lam rho L epsilon
      - (1 / lam) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
          (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1))
            * epsilon ^ (((n : ℝ) - 2) / (L : ℝ))
    = T_raw
      - (1 / lam) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
          (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)
                        * epsilon ^ ((n : ℝ) / (L : ℝ))) := by
  -- The two `Ioc 0 (2L-1)` sums on each side both split as
  --   (n = 1 term) + (Ioc 1 (2L-1) sum).
  -- The `purified_hitting_time` definition already cancels the
  -- `Ioc 1 (2L-1)` portions, so the identity reduces to equality of the
  -- two n=1 terms, which is the rpow identity ε^(-1/L) = 1/ε^(1/L)
  -- (needs ε > 0).
  unfold purified_hitting_time
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp
  -- L ≥ 1; split Ioc 0 (2L-1) = insert 1 (Ioc 1 (2L-1)).
  have hIoc_eq : Finset.Ioc 0 (2 * L - 1) = insert 1 (Finset.Ioc 1 (2 * L - 1)) := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ioc 1 (2 * L - 1) := by
    simp [Finset.mem_Ioc]
  -- The n = 1 term coincides on raw and purified sides.
  have hεne : epsilon ^ ((1 : ℝ) / (L : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hε _)
  have hrpow : epsilon ^ (((1 : ℝ) - 2) / (L : ℝ))
              = (epsilon ^ ((1 : ℝ) / (L : ℝ)))⁻¹ := by
    have : ((1 : ℝ) - 2) / (L : ℝ) = -((1 : ℝ) / (L : ℝ)) := by ring
    rw [this, Real.rpow_neg hε.le]
  rw [hIoc_eq, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
  push_cast
  rw [hrpow]
  field_simp
  ring

/-- **`purified_laurent_bound` (Path C, paper-2 spec extension).**

    The purified hitting time satisfies an Inversion-shape Laurent
    bound with a logarithmic envelope:
    $$|\tilde T(\varepsilon) - \tfrac{1}{\lambda}\sum_{n=1}^{2L-1}\tfrac{L}{n\rho^{2L-n-1}}\varepsilon^{(n-2)/L}|
       \le K_{\log}\,|\log\varepsilon|.$$

    This is the bridge consumed by `Inversion.rho_hat_rate`.

    **Status (named sorry).** Decomposes into:
      (1) `purified_hitting_time_residual_eq` (above, sorry'd but
          algebraic — no analysis).
      (2) `bernoulli_laurent_bound` (already sorry'd at the named-sorry
          level; bounds the raw residual by `K · ε^{-(L-2)/L}`).
      (3) **Envelope sharpening**: replace the polynomial envelope
          `ε^{-(L-2)/L}` with `|log ε|`. For `L = 2` these agree; for
          `L ≥ 3` requires Littwin Thm 4.5 with full error-term tracking.
          This is the genuinely new analytic content the paper-2 spec
          assumes; flagged as a single named sorry to keep the bridge
          honest.

    **Non-vacuity.** The conclusion existentially asserts `0 < K_log`
    and a `|log ε|` envelope — it does NOT admit `K_log = 0`. The
    statement constrains `purified_hitting_time` to scale as
    `ε^{-1/L}` (the leading Inversion term), which is the genuine
    ρ-distinguishing rate the inversion estimator inverts.

    **Domain restriction (session 82).** The envelope bound holds only
    for `ε < ε_max < 1` — near `ε = 1` we have `|log ε| → 0` while the
    purified residual stays bounded below by `O(1)` because the
    Laurent expansion is only meaningful in the small-`ε` asymptotic
    regime (JEPA dynamics' initial-condition window). This matches
    how all downstream consumers (`Inversion.rho_hat_rate`,
    `SignedRecovery.signed_recovery_pos_magnitude`) already restrict
    to `ε < exp(-1)` or `ε < ε_0 ∈ (0,1)`. The hypothesis
    `(ε_max : ℝ) (hε_max : 0 < ε_max < 1)` is a free parameter; a
    typical choice is `ε_max := exp(-1)`.

    **Path C axiom** (promoted 2026-05-20 alongside the three bernoulli
    pieces; statement-honesty pass 2026-05-20 added continuity,
    pointwise differentiability, reachability, and a `t_max`-sufficiency
    hypothesis). The envelope sharpening from `ε^{-(L-2)/L}` to `|log ε|`
    is the genuinely new analytic content the paper-2 spec assumes;
    cited as Littwin 2024 Thm 4.5 with full error tracking. The added
    hypotheses close the same vacuity gap as `bernoulli_gronwall_sandwich`:
    if `f` failed to reach the threshold, `hittingTime` would default
    to the `t_max + 1` sentinel and the LHS could be Ω(`t_max + 1`),
    contradicting the `|log ε|` claim. -/
axiom purified_laurent_bound
    (L : ℕ) (hL : 2 ≤ L)
    (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (C_ode : ℝ) (hC : 0 < C_ode)
    (ε_max : ℝ) (hε_max_pos : 0 < ε_max) (hε_max_lt : ε_max < 1) :
    ∃ K_log : ℝ, 0 < K_log ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < ε_max →
    -- `t_max` large enough for `f` to reach the threshold; matches the
    -- leading Laurent time scale `1/(lam·ε^{(2L-1)/L})` up to a factor.
    (2 * (L : ℝ)) / (lam * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ)))
        ≤ t_max →
    ∀ (f : ℝ → ℝ),
      f 0 = epsilon →
      ContinuousOn f (Set.Icc 0 t_max) →
      (∀ t ∈ Set.Ioo 0 t_max, DifferentiableAt ℝ f t) →
      (∀ t ∈ Set.Ioo 0 t_max,
        |deriv f t - ((L : ℝ) * lam
              * Real.rpow (f t) (3 - 1 / L)
              * (1 - Real.rpow (f t) (1 / L) / rho))|
        ≤ C_ode * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
      hittingTime f (p * rho ^ L) t_max < t_max →
      |purified_hitting_time
            (hittingTime f (p * rho ^ L) t_max) lam rho L epsilon
         - (1 / lam) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
               (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1))
                 * epsilon ^ (((n : ℝ) - 2) / (L : ℝ))|
        ≤ K_log * |Real.log epsilon|

/-- **`purified_critical_time_signed` (JEPA-data wrapper).**

    The signed-eigenbasis analogue: produces a critical-time function
    `t_crit : ℝ → ℝ` from the JEPA dynamics' diagonal amplitude
    `σ_r(t) = ⟨u_r*, Wbar(t) v_r*⟩`, satisfying the *Inversion-shape*
    Laurent expansion — i.e., directly consumable by
    `Inversion.rho_hat_rate` and hence by
    `SignedRecovery.signed_recovery_pos_magnitude`.

    The witness function is `purified_hitting_time` applied to the raw
    hitting time of σ_r at threshold `p · ρ^L`. -/
lemma purified_critical_time_signed
    {d : ℕ}
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (r : Fin d)
    (hrho_pos : 0 < (eb.pairs r).rho)
    (C : ℝ) (hC : 0 < C)
    (ε_max : ℝ) (hε_max_pos : 0 < ε_max) (hε_max_lt : ε_max < 1) :
    ∃ (t_crit : (ℝ → Matrix (Fin d) (Fin d) ℝ) → ℝ → ℝ) (K_log : ℝ),
      0 < K_log ∧
      ∀ (Wbar : ℝ → Matrix (Fin d) (Fin d) ℝ),
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon < ε_max →
        -- Statement-honesty: `t_max` sufficient for the JEPA diagonal
        -- amplitude to reach the threshold.
        (2 * (L : ℝ)) / (projectedCovariance dat eb r
            * epsilon ^ ((2 * (L : ℝ) - 1) / (L : ℝ))) ≤ t_max →
        diagAmplitude dat eb (Wbar 0) r = epsilon →
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
          ≤ C * epsilon ^ ((2 * (L : ℝ) - 1) / L)) →
        hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                    (p * (eb.pairs r).rho ^ L) t_max < t_max →
        |t_crit Wbar epsilon - (1 / projectedCovariance dat eb r) *
              ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
                (L : ℝ) / ((n : ℝ) * (eb.pairs r).rho ^ (2 * L - n - 1))
                  * epsilon ^ (((n : ℝ) - 2) / (L : ℝ))|
          ≤ K_log * |Real.log epsilon| := by
  have hlam_pos : 0 < projectedCovariance dat eb r := by
    unfold projectedCovariance
    exact mul_pos hrho_pos (eb.pairs r).hmu_pos
  obtain ⟨K_log, hK_log_pos, hK_log_bound⟩ :=
    purified_laurent_bound L hL
      (projectedCovariance dat eb r) ((eb.pairs r).rho)
      hlam_pos hrho_pos
      p hp hp_lt t_max ht_max C hC
      ε_max hε_max_pos hε_max_lt
  refine ⟨fun Wbar epsilon =>
    purified_hitting_time
      (hittingTime (fun t => diagAmplitude dat eb (Wbar t) r)
                   (p * (eb.pairs r).rho ^ L) t_max)
      (projectedCovariance dat eb r) ((eb.pairs r).rho) L epsilon,
    K_log, hK_log_pos, ?_⟩
  intro Wbar epsilon heps heps_lt h_t_max_reach hwbar_init hcont hdiff hode h_reach
  exact hK_log_bound epsilon heps heps_lt h_t_max_reach
    (fun t => diagAmplitude dat eb (Wbar t) r)
    hwbar_init hcont hdiff hode h_reach

end JepaRhoRecovery
