/-
# JepaRhoRecovery.Inversion

Layer 2.2: identifiability — inversion formula recovering ρ* from the
critical time $\tilde t_r^*$. Pure asymptotic analysis; no ODE machinery.

Positive-ρ branch only.

Proof source: proof_lecture.md Theorem 2.1.

CORRECTION: The original h_laurent exponent `ε ^ ((n : ℝ) / L)` was in the
denominator, yielding exponents `ε^{(1-n)/L}` after multiplication by `ε^{1/L}`—
these diverge for n ≥ 2 as ε → 0, making the theorem false. The corrected
version uses `ε ^ (((n : ℝ) - 2) / (L : ℝ))` as a factor (not denominator),
giving `ε^{(n-1)/L}` after multiplication so only the n = 1 constant survives.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

set_option maxHeartbeats 400000

open Real Finset Filter
open scoped Matrix

namespace JepaRhoRecovery

/-! ### Helper lemmas -/

/-
Reciprocal perturbation bound: |1/(1+u) - 1| ≤ 2|u| for |u| ≤ 1/2.
-/
lemma abs_inv_one_add_sub_one_le (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |1 / (1 + u) - 1| ≤ 2 * |u| := by
  cases abs_cases u <;> cases abs_cases ( 1 / ( 1 + u ) - 1 ) <;> nlinarith [ div_mul_cancel₀ 1 ( show ( 1 + u ) ≠ 0 by linarith ) ]

/-
Leading-term approximation (Steps 1–2 of the proof sketch).
    From the Laurent hypothesis, multiplication by `λ ε^{1/L}` extracts the
    n = 1 constant `A = L / ρ^{2L-2}` plus a remainder bounded by
    `D · ε^{1/L} · |log ε|`.
-/
lemma leading_term_approx
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hrho_pos : 0 < rho) (hlambda_pos : 0 < lambda)
    (t_crit : ℝ → ℝ)
    (K_log : ℝ) (hK_log_pos : 0 < K_log)
    (h_laurent : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_crit ε - (1 / lambda) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
            (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)) *
            ε ^ (((n : ℝ) - 2) / (L : ℝ))|
        ≤ K_log * |Real.log ε|) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      |lambda * t_crit ε * ε ^ ((1 : ℝ) / (L : ℝ)) -
        (L : ℝ) / rho ^ (2 * L - 2)|
        ≤ D * ε ^ ((1 : ℝ) / (L : ℝ)) * |Real.log ε| := by
  -- Use the Laurent hypothesis to bound the difference.
  have h_bound : ∀ ε, 0 < ε → ε < 1 → abs (lambda * t_crit ε * ε^(1 / (L : ℝ)) - L / rho^(2 * L - 2)) ≤ lambda * K_log * ε^(1 / (L : ℝ)) * abs (Real.log ε) + ∑ n ∈ Finset.Ioc 0 (2 * L - 1) \ {1}, (L / (n * rho^(2 * L - n - 1)) : ℝ) * ε^((n - 1) / (L : ℝ)) := by
    intro ε hε_pos hε_lt_1
    have h_bound_step : abs (lambda * t_crit ε * ε^(1 / (L : ℝ)) - ∑ n ∈ Finset.Ioc 0 (2 * L - 1), (L / (n * rho^(2 * L - n - 1)) : ℝ) * ε^((n - 1) / (L : ℝ))) ≤ lambda * K_log * ε^(1 / (L : ℝ)) * abs (Real.log ε) := by
      convert mul_le_mul_of_nonneg_left ( h_laurent ε hε_pos hε_lt_1 ) ( show 0 ≤ lambda * ε ^ ( 1 / ( L : ℝ ) ) by positivity ) using 1 <;> ring;
      rw [ show ( ∑ x ∈ Ioc 0 ( L * 2 - 1 ), ( L : ℝ ) * ( x : ℝ ) ⁻¹ * rho⁻¹ ^ ( L * 2 - x - 1 ) * ε ^ ( - ( L : ℝ ) ⁻¹ + ( L : ℝ ) ⁻¹ * x ) ) = ( ∑ x ∈ Ioc 0 ( L * 2 - 1 ), ( L : ℝ ) * rho⁻¹ ^ ( L * 2 - x - 1 ) * ( x : ℝ ) ⁻¹ * ε ^ ( - ( ( L : ℝ ) ⁻¹ * 2 ) + ( L : ℝ ) ⁻¹ * x ) ) * ε ^ ( ( L : ℝ ) ⁻¹ ) from ?_ ];
      · rw [ show lambda * t_crit ε * ε ^ ( L : ℝ ) ⁻¹ - ( ∑ x ∈ Ioc 0 ( L * 2 - 1 ), ( L : ℝ ) * rho⁻¹ ^ ( L * 2 - x - 1 ) * ( x : ℝ ) ⁻¹ * ε ^ ( - ( ( L : ℝ ) ⁻¹ * 2 ) + ( L : ℝ ) ⁻¹ * x ) ) * ε ^ ( L : ℝ ) ⁻¹ = lambda * ε ^ ( L : ℝ ) ⁻¹ * ( t_crit ε - lambda⁻¹ * ∑ x ∈ Ioc 0 ( L * 2 - 1 ), ( L : ℝ ) * rho⁻¹ ^ ( L * 2 - x - 1 ) * ( x : ℝ ) ⁻¹ * ε ^ ( - ( ( L : ℝ ) ⁻¹ * 2 ) + ( L : ℝ ) ⁻¹ * x ) ) by nlinarith [ mul_inv_cancel_left₀ hlambda_pos.ne' ( ∑ x ∈ Ioc 0 ( L * 2 - 1 ), ( L : ℝ ) * rho⁻¹ ^ ( L * 2 - x - 1 ) * ( x : ℝ ) ⁻¹ * ε ^ ( - ( ( L : ℝ ) ⁻¹ * 2 ) + ( L : ℝ ) ⁻¹ * x ) ), Real.rpow_pos_of_pos hε_pos ( L : ℝ ) ⁻¹ ] ] ; rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
      · rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ show ( - ( L : ℝ ) ⁻¹ + ( L : ℝ ) ⁻¹ * x : ℝ ) = - ( ( L : ℝ ) ⁻¹ * 2 ) + ( L : ℝ ) ⁻¹ * x + ( L : ℝ ) ⁻¹ by ring ] ; rw [ Real.rpow_add hε_pos ] ; ring;
    have h_bound_step : ∑ n ∈ Finset.Ioc 0 (2 * L - 1), (L / (n * rho^(2 * L - n - 1)) : ℝ) * ε^((n - 1) / (L : ℝ)) = L / rho^(2 * L - 2) + ∑ n ∈ Finset.Ioc 0 (2 * L - 1) \ {1}, (L / (n * rho^(2 * L - n - 1)) : ℝ) * ε^((n - 1) / (L : ℝ)) := by
      rw [ Finset.sum_eq_add_sum_diff_singleton ( show 1 ∈ Ioc 0 ( 2 * L - 1 ) from Finset.mem_Ioc.mpr ⟨ by norm_num, Nat.le_sub_one_of_lt ( by linarith ) ⟩ ) ] ; norm_num;
      rfl;
    rw [ abs_le ] at *;
    constructor <;> linarith [ show 0 ≤ ∑ n ∈ Finset.Ioc 0 ( 2 * L - 1 ) \ { 1 }, ( L : ℝ ) / ( n * rho ^ ( 2 * L - n - 1 ) ) * ε ^ ( ( n - 1 : ℝ ) / L ) from Finset.sum_nonneg fun _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho_pos.le _ ) ) ) ( Real.rpow_nonneg hε_pos.le _ ) ];
  -- Since ε < exp(-1), we have |log ε| > 1, thus ε^(1/L) * |log ε| ≥ ε^(1/L).
  have h_log_bound : ∀ ε, 0 < ε → ε < Real.exp (-1) → ∑ n ∈ Finset.Ioc 0 (2 * L - 1) \ {1}, (L / (n * rho^(2 * L - n - 1)) : ℝ) * ε^((n - 1) / (L : ℝ)) ≤ (∑ n ∈ Finset.Ioc 0 (2 * L - 1) \ {1}, (L / (n * rho^(2 * L - n - 1)) : ℝ)) * ε^(1 / (L : ℝ)) * |Real.log ε| := by
    intros ε hε_pos hε_lt_exp
    have h_log_bound : ∀ n ∈ Finset.Ioc 0 (2 * L - 1) \ {1}, ε^((n - 1) / (L : ℝ)) ≤ ε^(1 / (L : ℝ)) * |Real.log ε| := by
      intros n hn
      have h_exp_bound : ε^((n - 1) / (L : ℝ)) ≤ ε^(1 / (L : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_ge hε_pos ( by linarith [ Real.exp_le_one_iff.mpr ( show -1 ≤ 0 by norm_num ) ] ) ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne ( Finset.mem_Ioc.mp ( Finset.mem_sdiff.mp hn |>.1 ) |>.1 ) ( Ne.symm <| by aesop ) ] );
      exact le_trans h_exp_bound ( le_mul_of_one_le_right ( by positivity ) ( by rw [ abs_of_neg ( Real.log_neg hε_pos ( by linarith [ Real.exp_le_one_iff.mpr ( show -1 ≤ 0 by norm_num ) ] ) ) ] ; linarith [ Real.log_exp ( -1 ), Real.log_lt_log hε_pos hε_lt_exp ] ) );
    simpa only [ Finset.sum_mul _ _ _, mul_assoc ] using Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ( h_log_bound n hn ) ( by positivity );
  refine' ⟨ lambda * K_log + ∑ n ∈ Finset.Ioc 0 ( 2 * L - 1 ) \ { 1 }, ( L / ( n * rho ^ ( 2 * L - n - 1 ) ) : ℝ ) + 1, _, _ ⟩;
  · exact add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg hlambda_pos.le hK_log_pos.le ) ( Finset.sum_nonneg fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho_pos.le _ ) ) ) ) zero_lt_one;
  · intro ε hε₁ hε₂; specialize h_bound ε hε₁ ( hε₂.trans_le <| Real.exp_le_one_iff.mpr <| by norm_num ) ; specialize h_log_bound ε hε₁ hε₂; nlinarith [ show 0 ≤ ε ^ ( 1 / ( L : ℝ ) ) * |Real.log ε| by positivity ] ;

/-
Geometric sum lower bound for the algebraic factorization step.
    If `a ≥ b / 2` and `b > 0`, then
    `∑_{k=0}^{m-1} a^k b^{m-1-k} ≥ m * (b/2)^{m-1}`.
-/
lemma geom_sum₂_lower_bound (a b : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (ha : 0 < a) (hb : 0 < b) (hab : b / 2 ≤ a) :
    (m : ℝ) * (b / 2) ^ (m - 1) ≤
      ∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i) := by
  exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i hi => show a ^ i * b ^ ( m - 1 - i ) ≥ ( b / 2 ) ^ ( m - 1 ) from le_trans ( show ( b / 2 ) ^ ( m - 1 ) ≤ ( b / 2 ) ^ i * ( b / 2 ) ^ ( m - 1 - i ) by rw [ ← pow_add, add_tsub_cancel_of_le ( Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ] ) ( mul_le_mul ( pow_le_pow_left₀ ( by positivity ) hab _ ) ( pow_le_pow_left₀ ( by positivity ) ( show b / 2 ≤ b by linarith ) _ ) ( by positivity ) ( by positivity ) ) )

/-
Lipschitz-like bound for mth-root. Using geom_sum₂_mul factorization:
    if y/2 ≤ x and both positive, then
    |x^{1/m} - y^{1/m}| ≤ |x - y| / (m * (y^{1/m}/2)^{m-1}).
-/
lemma rpow_inv_sub_le (x y : ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hx : 0 < x) (hy : 0 < y) (hxy : y / 2 ≤ x) :
    |x ^ ((m : ℝ)⁻¹) - y ^ ((m : ℝ)⁻¹)| ≤
      |x - y| / ((m : ℝ) * (y ^ ((m : ℝ)⁻¹) / 2) ^ (m - 1)) := by
  have h_geom_sum : ∑ i ∈ Finset.range m, (x ^ (m : ℝ)⁻¹) ^ i * (y ^ (m : ℝ)⁻¹) ^ (m - 1 - i) ≥ m * (y ^ (m : ℝ)⁻¹ / 2) ^ (m - 1) := by
    -- Applying the geometric sum lower bound with $a = x^{1/m}$ and $b = y^{1/m}$, we need to show that $a \geq b/2$.
    have ha_ge_b_div_2 : x ^ (1 / (m : ℝ)) ≥ y ^ (1 / (m : ℝ)) / 2 := by
      refine' le_trans _ ( Real.rpow_le_rpow ( by positivity ) hxy ( by positivity ) );
      rw [ Real.div_rpow ( by positivity ) ( by positivity ) ];
      gcongr;
      exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( div_le_self ( by norm_num ) ( by norm_cast; linarith ) ) ) ( by norm_num );
    convert geom_sum₂_lower_bound ( x ^ ( m : ℝ ) ⁻¹ ) ( y ^ ( m : ℝ ) ⁻¹ ) m ( by linarith ) ( by positivity ) ( by positivity ) _ using 1 ; aesop;
  have h_geom_sum : (x ^ (m : ℝ)⁻¹ - y ^ (m : ℝ)⁻¹) * (∑ i ∈ Finset.range m, (x ^ (m : ℝ)⁻¹) ^ i * (y ^ (m : ℝ)⁻¹) ^ (m - 1 - i)) = x - y := by
    convert geom_sum₂_mul ( x ^ ( m : ℝ ) ⁻¹ ) ( y ^ ( m : ℝ ) ⁻¹ ) m using 1;
    · ring;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one, Real.rpow_one ];
  rw [ ← h_geom_sum, abs_mul, le_div_iff₀ ];
  · exact mul_le_mul_of_nonneg_left ( le_trans ‹_› ( le_abs_self _ ) ) ( abs_nonneg _ );
  · positivity

/-
The rpow identity: (ρ^{2L-2})^{1/(2L-2)} = ρ for ρ > 0 and L ≥ 2.
-/
lemma rho_pow_rpow_inv (rho : ℝ) (L : ℕ) (hrho : 0 < rho) (hL : 2 ≤ L) :
    (rho ^ (2 * L - 2)) ^ ((2 * (L : ℝ) - 2)⁻¹) = rho := by
  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), Nat.cast_sub ] <;> norm_num [ Nat.mul_succ, ( by linarith : 2 ≤ 2 * L ) ];
  rw [ mul_inv_cancel₀ ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ), Real.rpow_one ]

/-
Reciprocal difference bound: |1/(A+δ) - 1/A| ≤ 2|δ|/A² when |δ| ≤ A/2 and A > 0.
-/
lemma inv_perturbation_bound (A delta : ℝ) (hA : 0 < A) (hd : |delta| ≤ A / 2) :
    |1 / (A + delta) - 1 / A| ≤ 2 * |delta| / A ^ 2 := by
  rw [ div_sub_div ] <;> try linarith [ abs_le.mp hd ];
  norm_num [ abs_div, abs_mul ];
  rw [ abs_of_pos hA ];
  rw [ div_le_div_iff₀ ] <;> nlinarith [ abs_nonneg delta, abs_nonneg ( A + delta ), mul_le_mul_of_nonneg_left ( show |A + delta| ≥ A / 2 by cases abs_cases ( A + delta ) <;> linarith [ abs_le.mp hd ] ) hA.le ]

/-
For any positive D, bound, and L ≥ 2, ∃ ε₀ ∈ (0,1) such that
    D · ε^{1/L} · |log ε| ≤ bound for all ε ∈ (0, ε₀).
    Uses `tendsto_log_mul_rpow_nhdsGT_zero`.
-/
lemma choose_epsilon_bound (D bound : ℝ) (L : ℕ) (hD : 0 < D) (hbound : 0 < bound) (hL : 2 ≤ L) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        D * ε ^ ((1 : ℝ) / L) * |Real.log ε| ≤ bound := by
  -- Use the fact that $|log x * x^{1/L}| \to 0$ as $x \to 0+$.
  have h_log_mul_rpow_nhdsGT_zero : Filter.Tendsto (fun x => |Real.log x * x ^ (1 / (L : ℝ))|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := @tendsto_log_mul_rpow_nhdsGT_zero ( 1 / L ) ?_ <;> norm_num at *;
    · simpa [ abs_mul ] using this.abs;
    · grind;
  -- By the definition of limit, there exists a δ > 0 such that for all x ∈ (0, δ), |log x * x^(1/L)| < bound/D.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x : ℝ, 0 < x → x < δ → |Real.log x * x ^ (1 / (L : ℝ))| < bound / D := by
    have := Metric.tendsto_nhdsWithin_nhds.mp h_log_mul_rpow_nhdsGT_zero ( bound / D ) ( by positivity );
    exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ => by simpa using this.choose_spec.2 hx₁ ( by simpa [ abs_of_pos hx₁ ] using hx₂ ) ⟩;
  exact ⟨ Min.min δ ( 1 / 2 ), lt_min hδ_pos ( by norm_num ), lt_of_le_of_lt ( min_le_right _ _ ) ( by norm_num ), fun ε hε₁ hε₂ => by have := hδ ε hε₁ ( lt_of_lt_of_le hε₂ ( min_le_left _ _ ) ) ; rw [ lt_div_iff₀' hD ] at this; rw [ abs_mul, abs_of_nonneg ( Real.rpow_nonneg hε₁.le _ ) ] at this; ring_nf at *; linarith ⟩

/-
**Theorem 2.2 (Identifiability inversion formula).**

    Given the Laurent expansion of the critical time
    (corrected exponent — see file header), the estimator
    `ρ̂(ε) := (L / (λ · t_crit ε · ε^{1/L}))^{1/(2L-2)}`
    recovers `ρ` at rate `O(ε^{1/L} |log ε|)` as `ε → 0⁺`.
-/
theorem rho_hat_rate
    (L : ℕ) (hL : 2 ≤ L)
    (lambda rho : ℝ) (hrho_pos : 0 < rho) (hlambda_pos : 0 < lambda)
    (t_crit : ℝ → ℝ)
    (K_log : ℝ) (hK_log_pos : 0 < K_log)
    (h_laurent : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |t_crit ε - (1 / lambda) * ∑ n ∈ Finset.Ioc 0 (2 * L - 1),
            (L : ℝ) / ((n : ℝ) * rho ^ (2 * L - n - 1)) *
            ε ^ (((n : ℝ) - 2) / (L : ℝ))|
        ≤ K_log * |Real.log ε|) :
    ∃ ε_0 C : ℝ, 0 < ε_0 ∧ ε_0 < 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε_0 →
        |((L : ℝ) / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) ^
                   ((1 : ℝ) / (2 * (L : ℝ) - 2))
         - rho|
          ≤ C * ε ^ ((1 : ℝ) / L) * |Real.log ε| := by
  -- Set A := (L : ℝ) / rho^{2L-2}. Note A > 0 by positivity. Note L/A = rho^{2L-2}.
  set A := (L : ℝ) / rho ^ (2 * L - 2) with hA_def
  have hA_pos : 0 < A := by
    positivity
  have hL_div_A : L / A = rho ^ (2 * L - 2) := by
    rw [ div_div_eq_mul_div, mul_div_cancel_left₀ _ ( by positivity ) ];
  -- Choose ε₁ from choose_epsilon_bound with bound = min(A/2, rho^{2L-2}/2).
  obtain ⟨ε₁, hε₁_pos, hε₁_lt_one, hε₁_bound⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → (abs ((lambda * t_crit ε) * ε ^ ((1 : ℝ) / L) - A)) ≤ min (A / 2) (rho ^ (2 * L - 2) / 2) := by
    obtain ⟨D, hD_pos, hD⟩ := leading_term_approx L hL lambda rho hrho_pos hlambda_pos t_crit K_log hK_log_pos h_laurent;
    obtain ⟨ε₁, hε₁_pos, hε₁_lt_one, hε₁_bound⟩ := choose_epsilon_bound D (min (A / 2) (rho ^ (2 * L - 2) / 2)) L hD_pos (by
    exact lt_min ( half_pos hA_pos ) ( half_pos ( pow_pos hrho_pos _ ) )) hL;
    exact ⟨ Min.min ε₁ ( Real.exp ( -1 ) / 2 ), lt_min hε₁_pos ( by positivity ), lt_of_le_of_lt ( min_le_left _ _ ) hε₁_lt_one, fun ε hε₁ hε₂ => le_trans ( hD ε hε₁ ( by linarith [ min_le_right ε₁ ( Real.exp ( -1 ) / 2 ), Real.exp_pos ( -1 ) ] ) ) ( hε₁_bound ε hε₁ ( by linarith [ min_le_left ε₁ ( Real.exp ( -1 ) / 2 ), Real.exp_pos ( -1 ) ] ) ) ⟩;
  -- Choose ε₀ = min(ε₁, exp(-1)/2).
  obtain ⟨ε₀, hε₀_pos, hε₀_lt_one, hε₀_bound⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (abs ((lambda * t_crit ε) * ε ^ ((1 : ℝ) / L) - A)) ≤ min (A / 2) (rho ^ (2 * L - 2) / 2) ∧
    (abs ((lambda * t_crit ε) * ε ^ ((1 : ℝ) / L) - A)) ≤
      (leading_term_approx L hL lambda rho hrho_pos hlambda_pos t_crit K_log hK_log_pos h_laurent).choose *
      ε ^ ((1 : ℝ) / L) * (abs (Real.log ε)) := by
        use min ε₁ (Real.exp (-1) / 2);
        refine' ⟨ lt_min hε₁_pos ( by positivity ), min_lt_of_left_lt hε₁_lt_one, fun ε hε₁ hε₂ => ⟨ hε₁_bound ε hε₁ ( lt_of_lt_of_le hε₂ ( min_le_left _ _ ) ), _ ⟩ ⟩;
        grind;
  -- Apply the rpow_inv_sub_le lemma with x = base, y = rho^{2L-2}, and m = 2L-2.
  have h_rpow_inv_sub_le : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) ^ ((1 : ℝ) / (2 * L - 2)) - (rho ^ (2 * L - 2)) ^ ((1 : ℝ) / (2 * L - 2)))) ≤
    (abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (rho ^ (2 * L - 2)))) /
    ((2 * L - 2) * ((rho ^ (2 * L - 2)) ^ ((1 : ℝ) / (2 * L - 2)) / 2) ^ (2 * L - 3)) := by
      intros ε hε_pos hε_lt_ε₀
      have h_base_pos : 0 < L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) := by
        have := hε₀_bound ε hε_pos hε_lt_ε₀;
        exact div_pos ( by positivity ) ( by linarith [ abs_le.mp this.1, min_le_left ( A / 2 ) ( rho ^ ( 2 * L - 2 ) / 2 ), min_le_right ( A / 2 ) ( rho ^ ( 2 * L - 2 ) / 2 ) ] )
      have h_base_ge_half : L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) ≥ rho ^ (2 * L - 2) / 2 := by
        have := hε₀_bound ε hε_pos hε_lt_ε₀ |>.1;
        rw [ ge_iff_le, div_le_div_iff₀ ] <;> try positivity;
        · rw [ abs_le ] at this;
          cases min_cases ( A / 2 ) ( rho ^ ( 2 * L - 2 ) / 2 ) <;> nlinarith [ show ( L : ℝ ) ≥ 2 by norm_cast, show ( rho ^ ( 2 * L - 2 ) : ℝ ) > 0 by positivity, mul_div_cancel₀ ( L : ℝ ) ( show ( rho ^ ( 2 * L - 2 ) : ℝ ) ≠ 0 by positivity ) ];
        · grind +locals;
      convert rpow_inv_sub_le _ _ _ _ _ _ _ using 1;
      any_goals exact h_base_ge_half;
      any_goals positivity;
      any_goals exact 2 * L - 2;
      · rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring;
      · rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring;
        rfl;
      · omega;
  -- Apply the inv_perturbation_bound lemma with A = rho^{2L-2} and δ = lambda * t_crit ε * ε ^ ((1 : ℝ) / L) - A.
  have h_inv_perturbation_bound : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (rho ^ (2 * L - 2)))) ≤
    (2 * L * (leading_term_approx L hL lambda rho hrho_pos hlambda_pos t_crit K_log hK_log_pos h_laurent).choose) *
    ε ^ ((1 : ℝ) / L) * (abs (Real.log ε)) / A ^ 2 := by
      intros ε hε_pos hε_lt_ε₀
      have h_inv_perturbation_bound_step : abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (L / A)) ≤ 2 * L * abs ((lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) - A) / A ^ 2 := by
        have h_inv_perturbation_bound_step : abs ((1 / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (1 / A)) ≤ 2 * abs ((lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) - A) / A ^ 2 := by
          have h_inv_perturbation_bound_step : abs ((1 / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (1 / A)) ≤ 2 * abs ((lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) - A) / A ^ 2 := by
            have h_abs : abs ((lambda * t_crit ε * ε ^ ((1 : ℝ) / L)) - A) ≤ A / 2 := by
              exact le_trans ( hε₀_bound ε hε_pos hε_lt_ε₀ |>.1 ) ( min_le_left _ _ )
            convert inv_perturbation_bound A ( lambda * t_crit ε * ε ^ ( 1 / ( L : ℝ ) ) - A ) hA_pos h_abs using 1 ; ring;
          exact h_inv_perturbation_bound_step;
        convert mul_le_mul_of_nonneg_left h_inv_perturbation_bound_step ( Nat.cast_nonneg L ) using 1 <;> ring;
        rw [ show ( L : ℝ ) * lambda⁻¹ * ( t_crit ε ) ⁻¹ * ( ε ^ ( L : ℝ ) ⁻¹ ) ⁻¹ - L * A⁻¹ = L * ( lambda⁻¹ * ( t_crit ε ) ⁻¹ * ( ε ^ ( L : ℝ ) ⁻¹ ) ⁻¹ - A⁻¹ ) by ring, abs_mul, abs_of_nonneg ( by positivity ) ];
      simp_all +decide [ mul_assoc, div_eq_mul_inv ];
      exact h_inv_perturbation_bound_step.trans ( by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( hε₀_bound ε hε_pos hε_lt_ε₀ |>.2 ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) );
  -- Combine the bounds from h_rpow_inv_sub_le and h_inv_perturbation_bound.
  have h_combined_bound : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) ^ ((1 : ℝ) / (2 * L - 2)) - rho)) ≤
    (2 * L * (leading_term_approx L hL lambda rho hrho_pos hlambda_pos t_crit K_log hK_log_pos h_laurent).choose) /
    (A ^ 2 * ((2 * L - 2) * ((rho ^ (2 * L - 2)) ^ ((1 : ℝ) / (2 * L - 2)) / 2) ^ (2 * L - 3))) *
    ε ^ ((1 : ℝ) / L) * (abs (Real.log ε)) := by
      intros ε hε_pos hε_lt_ε₀
      specialize h_rpow_inv_sub_le ε hε_pos hε_lt_ε₀
      specialize h_inv_perturbation_bound ε hε_pos hε_lt_ε₀
      have h_combined : abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) ^ ((1 : ℝ) / (2 * L - 2)) - rho) ≤
        (abs ((L / (lambda * t_crit ε * ε ^ ((1 : ℝ) / L))) - (rho ^ (2 * L - 2)))) /
        ((2 * L - 2) * ((rho ^ (2 * L - 2)) ^ ((1 : ℝ) / (2 * L - 2)) / 2) ^ (2 * L - 3)) := by
          convert h_rpow_inv_sub_le using 2;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), Nat.cast_sub ( by linarith ), Nat.cast_mul, Nat.cast_two, mul_comm ] ; norm_num [ show ( L : ℝ ) ≠ 0 by positivity ];
          rw [ mul_inv_cancel₀ ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ), Real.rpow_one ];
      convert h_combined.trans ( div_le_div_of_nonneg_right h_inv_perturbation_bound <| mul_nonneg ( sub_nonneg.mpr <| by norm_cast; linarith ) <| pow_nonneg ( div_nonneg ( Real.rpow_nonneg ( pow_nonneg hrho_pos.le _ ) _ ) zero_le_two ) _ ) using 1 ; ring;
      grind;
  refine' ⟨ ε₀, _, hε₀_pos, hε₀_lt_one, _, fun ε hε₁ hε₂ => h_combined_bound ε hε₁ hε₂ ⟩;
  refine' div_pos _ _;
  · exact mul_pos ( by positivity ) ( leading_term_approx L hL lambda rho hrho_pos hlambda_pos t_crit K_log hK_log_pos h_laurent |> Classical.choose_spec |> And.left );
  · exact mul_pos ( sq_pos_of_pos hA_pos ) ( mul_pos ( by linarith [ show ( L : ℝ ) ≥ 2 by norm_cast ] ) ( pow_pos ( div_pos ( Real.rpow_pos_of_pos ( pow_pos hrho_pos _ ) _ ) zero_lt_two ) _ ) )

end JepaRhoRecovery