/-
# JepaRhoRecovery.ZeroBranchResidual

Tracker item #9 (AIS2026 rebuttal) — checking whether the zero-branch
ceiling claim of the paper's Theorem 6(ii) ("|σ_r(t)| = O(ε^{1/L}) for
all t, the bracket damps any positive growth") survives once the
residual term `R_r` from `DiagonalODE.generalised_diagonal_ODE` is
actually included, rather than the idealised `σ̇ = 0` placeholder
currently used by `SignedODE.sigma_zero_branch_constant`.

Hand derivation (session notes, not yet Lean-checked): at ρ* = 0 the
diagonal ODE is

    σ̇(t) = -L·μ·σ(t)^{(2 - 1/L) + L} + R(t),   |R(t)| ≤ C_R·ε^{(2L-1)/L}.

Comparing the decay term to the residual bound *at the initialisation
scale* σ = ε^{1/L}: the decay term scales as ε^{p/L} with
`p := (2 - 1/L) + L`, and the residual scales as ε^{(2L-1)/L}. Decay
dominates (ceiling self-consistent) iff `p/L < (2L-1)/L`, i.e. iff
`L² - 3L + 1 > 0`, i.e. `L > (3+√5)/2 ≈ 2.618`. For integer L this holds
for L ≥ 3 but **fails at L = 2** — the paper's only empirically-tested
depth (§10). At L = 2: decay term ~ ε^{1.75}, residual bound ~ ε^{1.5};
the residual is asymptotically the larger term, so nothing in the ODE
itself prevents the residual from pushing σ past its initial O(ε^{1/2})
scale.

This file asks Aristotle to check the L = 2 case directly: does there
exist an admissible residual R(t) (i.e. one respecting the stated bound)
under which σ is forced above K·√ε for every constant K, given enough
time within the trajectory horizon? A constructive positive answer
(exhibiting R ≡ +C_R·ε^{1.5} and showing σ must cross K·√ε) would show
the ceiling claim needs a corrected constant/exponent for L = 2 — i.e.
that this branch of Theorem 6(ii)'s current Lean backing
(`sigma_zero_branch_constant`, which assumes `HasDerivAt σ 0 t`) does not
carry over to the real perturbed dynamics, and that the paper's Remark
"Open: finite-time noise-aware classifier" is doing necessary, not
merely cautious, work at L = 2.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real

namespace JepaRhoRecovery

/- **L = 2 zero-branch residual-instability check.**

    Fix `μ > 0` (the eigenbasis weight) and `C_R > 0` (the residual
    constant of `DiagonalODE.generalised_diagonal_ODE`). Take the
    *constant* worst-case residual `R(t) ≡ C_R · ε^{3/2}` (admissible:
    `|R(t)| ≤ C_R · ε^{3/2}` trivially) and the L = 2 zero-branch ODE

        σ̇(t) = -2μ · σ(t)^{3.5} + C_R · ε^{3/2}.

    Claim: for every constant `K > 0`, there is `ε_0 > 0` such that for
    every `ε ∈ (0, ε_0)` and every trajectory `σ` on `[0, t_max]` with
    `t_max ≥ ε⁻¹` (comfortably inside the paper's
    `t_max* = poly(ε^{-1/L})` horizon at L = 2, since `ε^{-1/2} ≪ ε^{-1}`
    is the *shorter* bound and this claim only needs the *longer* one)
    satisfying this ODE with `0 < σ(0) ≤ √ε`, the trajectory is forced
    above `K · √ε` at some point in `[0, t_max]`.

    If this is provable, it demonstrates the zero-branch ceiling fails at
    L = 2 under the actual (residual-bearing) dynamics: σ does not stay
    within any fixed multiple of its initial O(√ε) scale.

    ────────────────────────────────────────────────────────────────────
    CORRECTION (Aristotle): the statement below with horizon
    `t_max ≥ ε⁻¹` is **false** for large `K`. Indeed, for `σ > 0` the ODE
    gives `σ̇ = -2μσ^{3.5} + C_R ε^{3/2} ≤ C_R ε^{3/2}`, hence
    `σ(t) ≤ σ(0) + C_R ε^{3/2}·t`. At `t = ε⁻¹` this caps every admissible
    trajectory at `σ ≤ σ(0) + C_R√ε ≤ (1 + C_R)√ε`. So for any
    `K > 1 + C_R` no trajectory can reach `K√ε` within `[0, ε⁻¹]`,
    independently of how small `ε` is. The mistake is a swept-under
    constant: the residual pushes `σ` upward at rate `≈ C_R ε^{3/2}`, so
    crossing the level `K√ε` genuinely needs time `≈ (2K/C_R)·ε⁻¹`, a
    `K`-dependent multiple of `ε⁻¹` (still `poly(ε^{-1/2})`, hence within
    the paper's horizon).

    The original statement is preserved (commented out) below, followed by
    the corrected version `zero_branch_L2_ceiling_violation`, whose only
    change is the horizon hypothesis `t_max ≥ (2K/C_R)·ε⁻¹`. The corrected
    version still establishes the ceiling violation for *every* `K`, so
    the qualitative conclusion (σ escapes any fixed multiple of √ε at
    L = 2 under residual-bearing dynamics) stands. -/

/- ORIGINAL (false as stated — see CORRECTION above):
theorem zero_branch_L2_ceiling_violation
    (mu C_R : ℝ) (hmu_pos : 0 < mu) (hCR_pos : 0 < C_R)
    (K : ℝ) (hK_pos : 0 < K) :
    ∃ eps_0 : ℝ, 0 < eps_0 ∧
      ∀ eps : ℝ, 0 < eps → eps < eps_0 →
        ∀ t_max : ℝ, t_max ≥ eps⁻¹ →
          ∀ sigma : ℝ → ℝ,
            0 < sigma 0 → sigma 0 ≤ Real.sqrt eps →
            ContinuousOn sigma (Set.Icc 0 t_max) →
            (∀ t ∈ Set.Ico 0 t_max, 0 < sigma t) →
            (∀ t ∈ Set.Ioo 0 t_max,
              HasDerivAt sigma
                (-(2 * mu) * Real.rpow (sigma t) (3.5 : ℝ)
                  + C_R * Real.rpow eps (3 / 2 : ℝ)) t) →
            ∃ t ∈ Set.Icc 0 t_max, sigma t > K * Real.sqrt eps := by
  sorry
-/

/-- Once `ε` is small enough, on the whole window `0 < s ≤ K√ε` the decay
    term `2μ s^{3.5}` is dominated by half the residual `C_R ε^{3/2}`, so
    the ODE right-hand side stays `≥ (C_R/2)·ε^{3/2}`. This is the L = 2
    scale separation `s^{3.5} ≤ (K√ε)^{3.5} = K^{3.5} ε^{1.75} ≪ ε^{1.5}`. -/
lemma zero_branch_decay_dominated
    (mu C_R K : ℝ) (hmu_pos : 0 < mu) (hCR_pos : 0 < C_R) (hK_pos : 0 < K)
    (eps : ℝ) (heps_pos : 0 < eps)
    (heps_lt : eps < (C_R / (4 * mu * Real.rpow K (3.5 : ℝ))) ^ (4 : ℕ))
    (s : ℝ) (hs_pos : 0 < s) (hs_le : s ≤ K * Real.sqrt eps) :
    (C_R / 2) * Real.rpow eps (3 / 2 : ℝ)
      ≤ -(2 * mu) * Real.rpow s (3.5 : ℝ) + C_R * Real.rpow eps (3 / 2 : ℝ) := by
  -- Reduces to `2μ s^{3.5} ≤ (C_R/2) ε^{3/2}`; the decay term at the top of the
  -- window is `2μ (K√ε)^{3.5} = 2μ K^{3.5} ε^{7/4}`, and `ε^{7/4} = ε^{3/2}·ε^{1/4}`
  -- with `ε^{1/4} ≤ C_R/(4μ K^{3.5})` for `ε` below the threshold.
  change (C_R / 2) * eps ^ (3/2:ℝ) ≤ -(2*mu) * s ^ (3.5:ℝ) + C_R * eps ^ (3/2:ℝ)
  have hKp : (0:ℝ) < K ^ (3.5:ℝ) := Real.rpow_pos_of_pos hK_pos _
  have hden : (0:ℝ) < 4 * mu * K ^ (3.5:ℝ) := by positivity
  set A := C_R / (4 * mu * K ^ (3.5:ℝ)) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have heps_lt' : eps < A ^ (4:ℕ) := heps_lt
  have h14 : eps ^ ((4:ℝ)⁻¹) ≤ A := by
    have hmono := Real.rpow_le_rpow (le_of_lt heps_pos) (le_of_lt heps_lt')
      (by positivity : (0:ℝ) ≤ ((4:ℕ):ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (le_of_lt hApos) (by norm_num)] at hmono
    simpa using hmono
  have hs35 : s ^ (3.5:ℝ) ≤ K ^ (3.5:ℝ) * eps ^ (7/4:ℝ) := by
    have h1 : s ^ (3.5:ℝ) ≤ (K * Real.sqrt eps) ^ (3.5:ℝ) :=
      Real.rpow_le_rpow (le_of_lt hs_pos) hs_le (by norm_num)
    have h2 : (K * Real.sqrt eps) ^ (3.5:ℝ) = K ^ (3.5:ℝ) * eps ^ (7/4:ℝ) := by
      rw [Real.mul_rpow (le_of_lt hK_pos) (Real.sqrt_nonneg eps), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (le_of_lt heps_pos)]
      norm_num
    rw [h2] at h1; exact h1
  have hsplit : eps ^ (7/4:ℝ) = eps ^ (3/2:ℝ) * eps ^ ((4:ℝ)⁻¹) := by
    rw [← Real.rpow_add heps_pos]; norm_num
  have hAeq : 2 * mu * K ^ (3.5:ℝ) * A = C_R / 2 := by
    rw [hA]; field_simp; ring
  have key : 2 * mu * s ^ (3.5:ℝ) ≤ (C_R / 2) * eps ^ (3/2:ℝ) := by
    have hfac : 2 * mu * K ^ (3.5:ℝ) * eps ^ (3/2:ℝ) ≥ 0 := by positivity
    calc 2 * mu * s ^ (3.5:ℝ)
        ≤ 2 * mu * (K ^ (3.5:ℝ) * eps ^ (7/4:ℝ)) := by nlinarith [hs35, hmu_pos]
      _ = (2 * mu * K ^ (3.5:ℝ) * eps ^ (3/2:ℝ)) * eps ^ ((4:ℝ)⁻¹) := by rw [hsplit]; ring
      _ ≤ (2 * mu * K ^ (3.5:ℝ) * eps ^ (3/2:ℝ)) * A := mul_le_mul_of_nonneg_left h14 hfac
      _ = (2 * mu * K ^ (3.5:ℝ) * A) * eps ^ (3/2:ℝ) := by ring
      _ = (C_R / 2) * eps ^ (3/2:ℝ) := by rw [hAeq]
  linarith [key]

/-- **L = 2 zero-branch residual-instability check (corrected horizon).**
    Same as the original claim but with the horizon `t_max ≥ (2K/C_R)·ε⁻¹`
    in place of `t_max ≥ ε⁻¹` (see the CORRECTION note above). For every
    `K > 0` there is `ε_0 > 0` so that for `ε ∈ (0, ε_0)` any trajectory of
    the L = 2 zero-branch ODE with `0 < σ(0) ≤ √ε` is forced above `K√ε`
    somewhere in `[0, t_max]`, i.e. the zero-branch O(√ε) ceiling fails. -/
theorem zero_branch_L2_ceiling_violation
    (mu C_R : ℝ) (hmu_pos : 0 < mu) (hCR_pos : 0 < C_R)
    (K : ℝ) (hK_pos : 0 < K) :
    ∃ eps_0 : ℝ, 0 < eps_0 ∧
      ∀ eps : ℝ, 0 < eps → eps < eps_0 →
        ∀ t_max : ℝ, t_max ≥ (2 * K / C_R) * eps⁻¹ →
          ∀ sigma : ℝ → ℝ,
            0 < sigma 0 → sigma 0 ≤ Real.sqrt eps →
            ContinuousOn sigma (Set.Icc 0 t_max) →
            (∀ t ∈ Set.Ico 0 t_max, 0 < sigma t) →
            (∀ t ∈ Set.Ioo 0 t_max,
              HasDerivAt sigma
                (-(2 * mu) * Real.rpow (sigma t) (3.5 : ℝ)
                  + C_R * Real.rpow eps (3 / 2 : ℝ)) t) →
            ∃ t ∈ Set.Icc 0 t_max, sigma t > K * Real.sqrt eps := by
  -- Take `eps_0 := (C_R / (4μ K^{3.5}))^4` (the `zero_branch_decay_dominated` threshold).
  -- By contradiction, if `σ ≤ K√ε` throughout `[0, t_max]`, the ODE right-hand side
  -- stays `≥ (C_R/2) ε^{3/2}` (by `zero_branch_decay_dominated`), so by the mean value
  -- theorem the total growth over `[0, t_max]` is `≥ (C_R/2) ε^{3/2} · t_max ≥ K√ε`,
  -- forcing `σ(t_max) > K√ε` — contradiction.
  refine ⟨(C_R / (4 * mu * Real.rpow K (3.5:ℝ))) ^ (4:ℕ), ?_, ?_⟩
  · have hk := Real.rpow_pos_of_pos hK_pos (3.5:ℝ)
    have hb : (0:ℝ) < C_R / (4 * mu * Real.rpow K (3.5:ℝ)) := by positivity
    exact pow_pos hb 4
  intro eps heps_pos heps_lt t_max ht_max sigma hs0_pos hs0_le hcont hpos hderiv
  by_contra hcon
  push_neg at hcon
  have htmax_pos : 0 < t_max := lt_of_lt_of_le (by positivity) ht_max
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope sigma
    (fun t => -(2*mu) * Real.rpow (sigma t) (3.5:ℝ) + C_R * Real.rpow eps (3/2:ℝ))
    htmax_pos hcont (fun t ht => hderiv t ht)
  simp only [sub_zero] at hc_eq
  have hc_pos : 0 < sigma c := hpos c ⟨le_of_lt hc_mem.1, hc_mem.2⟩
  have hc_le : sigma c ≤ K * Real.sqrt eps := hcon c ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
  have hdecay := zero_branch_decay_dominated mu C_R K hmu_pos hCR_pos hK_pos eps heps_pos heps_lt
    (sigma c) hc_pos hc_le
  have hslope : (C_R/2) * Real.rpow eps (3/2:ℝ) ≤ (sigma t_max - sigma 0)/t_max := by
    rw [← hc_eq]; exact hdecay
  rw [le_div_iff₀ htmax_pos] at hslope
  have hpow : Real.rpow eps (3/2:ℝ) * eps⁻¹ = Real.sqrt eps := by
    rw [show Real.rpow eps (3/2:ℝ) = eps ^ (3/2:ℝ) from rfl, Real.sqrt_eq_rpow,
      ← Real.rpow_neg_one eps, ← Real.rpow_add heps_pos]; norm_num
  have hCRne : C_R ≠ 0 := hCR_pos.ne'
  have h0 : (0:ℝ) ≤ (C_R/2) * Real.rpow eps (3/2:ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg heps_pos.le _)
  have hKid : (C_R/2) * (2*K/C_R) = K := by field_simp
  have hgrow : K * Real.sqrt eps ≤ (C_R/2) * Real.rpow eps (3/2:ℝ) * t_max := by
    have heq : (C_R/2) * Real.rpow eps (3/2:ℝ) * ((2*K/C_R)*eps⁻¹) = K * Real.sqrt eps := by
      calc (C_R/2) * Real.rpow eps (3/2:ℝ) * ((2*K/C_R)*eps⁻¹)
          = ((C_R/2)*(2*K/C_R)) * (Real.rpow eps (3/2:ℝ) * eps⁻¹) := by ring
        _ = K * Real.sqrt eps := by rw [hKid, hpow]
    calc K * Real.sqrt eps = (C_R/2) * Real.rpow eps (3/2:ℝ) * ((2*K/C_R)*eps⁻¹) := heq.symm
      _ ≤ (C_R/2) * Real.rpow eps (3/2:ℝ) * t_max := mul_le_mul_of_nonneg_left ht_max h0
  have hle := hcon t_max ⟨le_of_lt htmax_pos, le_refl t_max⟩
  linarith [hslope, hgrow, hs0_pos, hle]

end JepaRhoRecovery
