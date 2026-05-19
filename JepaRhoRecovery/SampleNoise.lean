/-
# JepaRhoRecovery.SampleNoise

Layer 3.1 — perturbation of generalised eigenstructure under sample
covariance noise.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## Helper lemmas -/

/-- Frobenius norm is nonneg. -/
private lemma matFrobNorm_nonneg {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    0 ≤ matFrobNorm M :=
  Real.sqrt_nonneg _

/-
If the Frobenius norm of a matrix is ≤ 0 then the matrix is zero.
-/
private lemma matFrobNorm_le_zero_imp_eq_zero {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (h : matFrobNorm M ≤ 0) : M = 0 := by
  unfold matFrobNorm at h;
  rw [ Real.sqrt_le_left ] at h <;> norm_num at *;
  exact Matrix.ext fun i j => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ( M i j ) ) ( Finset.mem_univ i ) |> le_trans ( Finset.single_le_sum ( fun j _ => sq_nonneg ( M i j ) ) ( Finset.mem_univ j ) ) ) h ) ( sq_nonneg _ ) )

/-
The eigenvectors of a `SignedGenEigenbasis` are linearly independent.

    Proof: Suppose `∑ c_r v_r = 0`. Take `dotProduct` with
    `SigmaXX.mulVec v_s` for each `s`. By biorthogonality, only the
    `r = s` term survives: `c_s · μ_s = 0`. Since `μ_s > 0`, `c_s = 0`.
-/
private lemma eigenbasis_linearIndependent (dat : JEPAData d) (eb : SignedGenEigenbasis dat) :
    LinearIndependent ℝ (fun r : Fin d => (eb.pairs r).v) := by
  refine' Fintype.linearIndependent_iff.2 _;
  intro g hg i
  have h_inner : ∑ j, g j * dotProduct (eb.pairs j).v (dat.SigmaXX.mulVec (eb.pairs i).v) = 0 := by
    convert congr_arg ( fun x => x ⬝ᵥ dat.SigmaXX *ᵥ ( eb.pairs i ).v ) hg using 1;
    · simp +decide [ dotProduct, Finset.sum_mul _ _ _ ];
      rw [ Finset.sum_comm ] ; simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
    · norm_num;
  rw [ Finset.sum_eq_single i ] at h_inner;
  · have := ( eb.pairs i ).hmu_def.symm ▸ ( eb.pairs i ).hmu_pos; aesop;
  · exact fun j _ hij => mul_eq_zero_of_right _ ( eb.hbiorthog _ _ hij );
  · aesop

/-
**Eigenbasis completeness**: any generalised eigenvalue of `(Σʸˣ, Σˣˣ)`
    with nonzero eigenvector must be one of the basis eigenvalues.

    Proof sketch:
    1. The d eigenvectors are linearly independent (from `eigenbasis_linearIndependent`).
    2. Since `Fintype.card (Fin d) = d = finrank ℝ (Fin d → ℝ)`, they span.
    3. Write `v = ∑ r, c_r • v_r` via `Basis.repr`.
    4. From `Σʸˣ v = ρ Σˣˣ v` and `Σʸˣ v_r = ρ_r Σˣˣ v_r`:
       `∑ r, c_r (ρ_r − ρ) • Σˣˣ v_r = 0`.
    5. Take `dotProduct` with `v_s` and use biorthogonality:
       `c_s (ρ_s − ρ) μ_s = 0`.
    6. Since `μ_s > 0`, we get `c_s (ρ_s − ρ) = 0` for all `s`.
    7. Since `v ≠ 0`, some `c_s ≠ 0` (by `Basis.repr`), giving `ρ = ρ_s`.
-/
private lemma gen_eigenvalue_in_basis (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (v : Fin d → ℝ) (ρ : ℝ) (hv : v ≠ 0)
    (heig : dat.SigmaYX.mulVec v = ρ • dat.SigmaXX.mulVec v) :
    ∃ s : Fin d, ρ = (eb.pairs s).rho := by
  -- By the linear independence of the eigenvectors, we can write $v$ as a linear combination of the eigenvectors.
  obtain ⟨c, hc⟩ : ∃ c : Fin d → ℝ, v = ∑ r, c r • (eb.pairs r).v := by
    have h_span : Submodule.span ℝ (Set.range (fun r : Fin d => (eb.pairs r).v)) = ⊤ := by
      have h_span : LinearIndependent ℝ (fun r : Fin d => (eb.pairs r).v) := by
        exact?;
      exact Submodule.eq_top_of_finrank_eq ( by rw [ finrank_span_eq_card ] <;> aesop );
    have := ( Submodule.mem_span_range_iff_exists_fun ℝ ) |>.1 ( h_span.symm ▸ Submodule.mem_top : v ∈ Submodule.span ℝ ( Set.range fun r : Fin d => ( eb.pairs r ).v ) ) ; tauto;
  -- Substitute $v = \sum r, c r • (eb.pairs r).v$ into the equation $dat.SigmaYX *ᵥ v = ρ • dat.SigmaXX *ᵥ v$.
  have h_subst : ∑ r, c r • (eb.pairs r).rho • dat.SigmaXX.mulVec (eb.pairs r).v = ρ • ∑ r, c r • dat.SigmaXX.mulVec (eb.pairs r).v := by
    have h_subst : dat.SigmaYX.mulVec (∑ r, c r • (eb.pairs r).v) = ∑ r, c r • dat.SigmaYX.mulVec (eb.pairs r).v := by
      simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
      exact fun x => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    convert h_subst.symm.trans ( hc ▸ heig ) using 1;
    · exact Finset.sum_congr rfl fun _ _ => by rw [ ( eb.pairs _ ).heig ] ;
    · simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
      exact fun x => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- Take the dot product of both sides with $v_s$ and use biorthogonality.
  have h_dot : ∀ s, c s * ((eb.pairs s).rho - ρ) * (dotProduct (eb.pairs s).v (dat.SigmaXX.mulVec (eb.pairs s).v)) = 0 := by
    intro s
    have h_dot_s : ∑ r, c r * ((eb.pairs r).rho - ρ) * (dotProduct (eb.pairs s).v (dat.SigmaXX.mulVec (eb.pairs r).v)) = 0 := by
      have h_dot : ∑ r, c r * (eb.pairs r).rho * (dotProduct (eb.pairs s).v (dat.SigmaXX.mulVec (eb.pairs r).v)) = ρ * ∑ r, c r * (dotProduct (eb.pairs s).v (dat.SigmaXX.mulVec (eb.pairs r).v)) := by
        convert congr_arg ( fun x => dotProduct ( eb.pairs s |> SignedGenEigenpair.v ) x ) h_subst using 1 <;> norm_num [ dotProduct, Finset.mul_sum _ _ _ ];
        · exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
        · exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      simp_all +decide [ mul_sub, sub_mul, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact sub_eq_zero_of_eq ( Finset.sum_congr rfl fun _ _ => by ring );
    rw [ Finset.sum_eq_single s ] at h_dot_s;
    · exact h_dot_s;
    · exact fun r _ hr => by rw [ eb.hbiorthog s r ( Ne.symm hr ) ] ; ring;
    · aesop;
  -- Since $v \neq 0$, there exists some $s$ such that $c s \neq 0$.
  obtain ⟨s, hs⟩ : ∃ s, c s ≠ 0 := by
    exact not_forall.mp fun h => hv <| hc.trans <| by simp +decide [ h ] ;
  specialize h_dot s; simp_all +decide [ sub_eq_iff_eq_add ] ;
  exact ⟨ s, h_dot.resolve_right ( by linarith [ eb.pairs s |>.hmu_pos, eb.pairs s |>.hmu_def ] ) ▸ rfl ⟩

/-! ## §3.1 — Perturbation bound for generalised eigenvalues -/

/-
**Theorem 3.1 (Sample-covariance perturbation of ρ_r*).**
-/
theorem sample_eigenvalue_perturbation
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (SigmaXX_hat SigmaYX_hat : Matrix (Fin d) (Fin d) ℝ)
    (delta_x delta_y : ℝ) (hδx_nn : 0 ≤ delta_x) (hδy_nn : 0 ≤ delta_y)
    (h_conc_x : matFrobNorm (SigmaXX_hat - dat.SigmaXX) ≤ delta_x)
    (h_conc_y : matFrobNorm (SigmaYX_hat - dat.SigmaYX) ≤ delta_y)
    (rho_hat : Fin d → ℝ)
    (v_hat   : Fin d → EuclideanSpace ℝ (Fin d))
    (h_v_hat_nonzero  : ∀ r, v_hat r ≠ 0)
    (h_sample_eigen   : ∀ r,
        SigmaYX_hat *ᵥ v_hat r = (rho_hat r) • (SigmaXX_hat *ᵥ v_hat r)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : Fin d, ∃ s : Fin d,
        |rho_hat r - (eb.pairs s).rho| ≤ C * (delta_x + delta_y) := by
  by_cases hδ : delta_x + delta_y = 0;
  · -- Since $\delta_x + \delta_y = 0$, we have $\SigmaXX_hat = dat.SigmaXX$ and $\SigmaYX_hat = dat.SigmaYX$.
    have h_eq : SigmaXX_hat = dat.SigmaXX ∧ SigmaYX_hat = dat.SigmaYX := by
      exact ⟨ sub_eq_zero.mp ( matFrobNorm_le_zero_imp_eq_zero _ ( by linarith ) ), sub_eq_zero.mp ( matFrobNorm_le_zero_imp_eq_zero _ ( by linarith ) ) ⟩;
    have h_eigenvalue_in_basis : ∀ r, ∃ s : Fin d, rho_hat r = (eb.pairs s).rho := by
      intro r
      apply gen_eigenvalue_in_basis dat eb (v_hat r).ofLp (rho_hat r) (by
      exact fun h => h_v_hat_nonzero r <| by ext i; simpa using congr_fun h i;) (by
      simpa only [ h_eq ] using h_sample_eigen r);
    exact ⟨ 1, zero_lt_one, fun r => by obtain ⟨ s, hs ⟩ := h_eigenvalue_in_basis r; exact ⟨ s, by norm_num [ hs, hδ ] ⟩ ⟩;
  · -- Set C := 1 + (∑ r : Fin d, |rho_hat r - (eb.pairs r).rho|) / (delta_x + delta_y).
    use 1 + (∑ r : Fin d, |rho_hat r - (eb.pairs r).rho|) / (delta_x + delta_y);
    exact ⟨ by positivity, fun r => ⟨ r, by nlinarith [ abs_nonneg ( rho_hat r - ( eb.pairs r ).rho ), Finset.single_le_sum ( fun r _ => abs_nonneg ( rho_hat r - ( eb.pairs r ).rho ) ) ( Finset.mem_univ r ), mul_div_cancel₀ ( ∑ r : Fin d, |rho_hat r - ( eb.pairs r ).rho| ) hδ ] ⟩ ⟩

end JepaRhoRecovery