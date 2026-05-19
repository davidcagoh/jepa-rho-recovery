/-
# JepaRhoRecovery.DiagonalODE

Layer 2.1 — generalised diagonal ODE. Derives the scalar ODE governing
σ_r(t) = uᵣᵀ W̄(t) vᵣ from the matrix gradient flow on W̄, modulo a small
off-diagonal remainder.

This is paper-2-grade content: paper-1 *assumes* the diagonal ODE (cf.
`jepa_bernoulli_solution`'s `hwbar_ode` hypothesis); Layer 2.1 is exactly the
derivation paper-1 skipped.

**Structure**

  * `BalancedInit` — Arora 2019 balanced-network predicate (non-vacuous).
  * `sigma_deriv_from_Wbar_flow` — chain rule giving σ̇_r as a function of
    Ẇ̄. Pure linearity, no analysis. Proved here.
  * `generalised_diagonal_ODE` — the main target. States that σ̇_r matches
    the closed-form `λ σ^{3-1/L} − λ σ³ / ρ` up to a remainder bounded by
    `K · ε^{(2L−1)/L}`. Sorry'd; Aristotle dispatch will follow once
    Layer 4.1 lands.

**Signed-first discipline:** `(eb.pairs r).rho` is signed; statements do not
bake positivity into types. The diagonal ODE is stated in a sign-agnostic
form — sign-branching is the job of Layer 4.1.
-/

import JepaRhoRecovery.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Filter Matrix
open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-! ## Balancedness (Arora 2019) -/

/-- **Balanced-network predicate.**
    The standard Arora 2019 balancedness condition: at every time `t`, the
    matrix `W̄(t)ᵀ W̄(t)` has the same eigenstructure as `W̄(t) W̄(t)ᵀ`,
    with squared singular values scaling as `σ_r(t)^{2 - 2/L}` along the
    generalised eigenbasis. In the linear-JEPA setting this is preserved
    under gradient flow once it holds at `t = 0`.

    The predicate is non-vacuous: it constrains the matrix structure
    concretely; no `True` placeholder. -/
def BalancedInit (L : ℕ) (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (Wbar : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ r : Fin d,
    dotProduct (dualBasis dat eb r)
        ((Wbarᵀ * Wbar).mulVec (eb.pairs r).v)
      = Real.rpow (diagAmplitude dat eb Wbar r)
          (2 * ((L : ℝ) - 1) / L)
        * (eb.pairs r).mu

/-! ## Chain rule: σ̇_r in terms of Ẇ̄ -/

/-- **Chain-rule lemma for σ_r.**  -/
lemma sigma_deriv_from_Wbar_flow
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (r : Fin d)
    (Wbar : ℝ → Matrix (Fin d) (Fin d) ℝ) (Wbar' : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (hWbar_deriv : HasDerivAt Wbar Wbar' t) :
    HasDerivAt (fun s => diagAmplitude dat eb (Wbar s) r)
      (dotProduct (dualBasis dat eb r) (Wbar'.mulVec (eb.pairs r).v)) t := by
  rw [ hasDerivAt_pi ] at *;
  have hWbar_deriv' : ∀ i j, HasDerivAt (fun s => Wbar s i j) (Wbar' i j) t := by
    exact fun i j => by simpa using HasDerivAt.comp t ( hasDerivAt_pi.1 ( hWbar_deriv i ) j ) ( hasDerivAt_id t ) ;
  convert HasDerivAt.sum fun i _ => HasDerivAt.const_mul ( dualBasis dat eb r i ) ( HasDerivAt.sum fun j _ => HasDerivAt.const_mul ( ( eb.pairs r ).v j ) ( hWbar_deriv' i j ) ) using 1;
  any_goals exact Finset.univ;
  any_goals exact fun _ => Finset.univ;
  · ext; simp +decide [ diagAmplitude, dotProduct, mul_comm ] ;
    rfl;
  · simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ]

/-! ## Helper lemmas for the generalised diagonal ODE -/

/-- The transpose-dotProduct identity: ⟨a, Mᵀ b⟩ = ⟨M a, b⟩. -/
lemma dotProduct_transpose_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d → ℝ) :
    dotProduct a (M.transpose.mulVec b) = dotProduct (M.mulVec a) b := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- Algebraic identity: applying `gradWbar` to the eigenvector `v_r` and taking the
    inner product with the dual basis vector `u_r` gives a specific bilinear expression.
    Uses the eigenvector relation `Σʸˣ v_r = ρ Σˣˣ v_r` and transpose identities. -/
lemma gradWbar_eigenvector_identity
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat) (r : Fin d)
    (W V_val : Matrix (Fin d) (Fin d) ℝ) :
    dotProduct (dualBasis dat eb r) ((gradWbar dat W V_val).mulVec (eb.pairs r).v) =
      dotProduct (V_val.mulVec (dualBasis dat eb r))
        (V_val.mulVec (W.mulVec (dualBasis dat eb r)) -
          (eb.pairs r).rho • W.mulVec (dualBasis dat eb r)) := by
  have h_gradWbar : (gradWbar dat W V_val).mulVec (eb.pairs r).v = V_val.transpose.mulVec ((V_val * W * dat.SigmaXX - W * dat.SigmaYX).mulVec (eb.pairs r).v) := by
    unfold gradWbar; aesop;
  rw [ h_gradWbar, dotProduct_transpose_mulVec ];
  simp +decide [ dualBasis, Matrix.sub_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (eb.pairs r).heig ];
  simp +decide [ ← Matrix.mulVec_mulVec, (eb.pairs r).heig, mul_assoc, Matrix.mulVec_smul ]

/-
**Eigenbasis completeness.** The generalised eigenvectors form a basis for ℝ^d
    (under the Σˣˣ inner product). Concretely, any vector `y` can be decomposed as
    `y = ∑ r, (⟨u_r, y⟩ / μ_r) • v_r`.
-/
lemma eigenbasis_completeness (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (y : Fin d → ℝ) :
    y = ∑ r : Fin d, ((dotProduct (dualBasis dat eb r) y) / (eb.pairs r).mu) • (eb.pairs r).v := by
  -- By the properties of the dual basis and the definition of the projection, we can expand y in terms of the dual basis.
  have h_expand : ∀ y : Fin d → ℝ, y = ∑ r, (dotProduct (dualBasis dat eb r) y / (eb.pairs r).mu) • (eb.pairs r).v := by
    intro y
    have h_basis : ∀ y : Fin d → ℝ, y = ∑ r, (dotProduct (eb.pairs r).v (dat.SigmaXX.mulVec y) / (eb.pairs r).mu) • (eb.pairs r).v := by
      intro y
      have h_basis : ∀ y : Fin d → ℝ, y = ∑ r, (dotProduct (eb.pairs r).v (dat.SigmaXX.mulVec y) / (eb.pairs r).mu) • (eb.pairs r).v := by
        intro y
        have h_lin_indep : LinearIndependent ℝ (fun r : Fin d => (eb.pairs r).v) := by
          refine' Fintype.linearIndependent_iff.2 _;
          intro g hg i
          have h_inner : ∀ j, dotProduct (eb.pairs j).v (dat.SigmaXX.mulVec (∑ i, g i • (eb.pairs i).v)) = g j * (eb.pairs j).mu := by
            intro j
            have h_inner : dotProduct (eb.pairs j).v (dat.SigmaXX.mulVec (∑ i, g i • (eb.pairs i).v)) = ∑ i, g i * dotProduct (eb.pairs j).v (dat.SigmaXX.mulVec (eb.pairs i).v) := by
              simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
              exact?;
            rw [ h_inner, Finset.sum_eq_single j ] <;> simp +contextual [ eb.hbiorthog, (eb.pairs j).hmu_def ];
            exact fun k hk => Or.inr <| eb.hbiorthog _ _ <| Ne.symm hk;
          simp_all +decide [ dotProduct ];
          exact Or.resolve_right ( h_inner i ) ( ne_of_gt ( eb.pairs i |>.hmu_pos ) )
        have h_basis : ∀ y : Fin d → ℝ, ∃ c : Fin d → ℝ, y = ∑ r, c r • (eb.pairs r).v := by
          have h_span : Submodule.span ℝ (Set.range (fun r : Fin d => (eb.pairs r).v)) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            rw [ finrank_span_eq_card ] <;> aesop;
          intro y; have := h_span.ge ( Submodule.mem_top : y ∈ ⊤ ) ; rw [ Submodule.mem_span_range_iff_exists_fun ] at this; tauto;
        obtain ⟨ c, rfl ⟩ := h_basis y;
        have h_coeff : ∀ r : Fin d, dotProduct (eb.pairs r).v (dat.SigmaXX.mulVec (∑ s, c s • (eb.pairs s).v)) = c r * (eb.pairs r).mu := by
          intro r
          have h_coeff : dotProduct (eb.pairs r).v (dat.SigmaXX.mulVec (∑ s, c s • (eb.pairs s).v)) = ∑ s, c s * dotProduct (eb.pairs r).v (dat.SigmaXX.mulVec (eb.pairs s).v) := by
            simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
            exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
          rw [ h_coeff, Finset.sum_eq_single r ] <;> simp_all +decide [ dotProduct_comm ];
          · exact Or.inl ( by rw [ ( eb.pairs r ).hmu_def ] );
          · exact fun s hs => Or.inr <| eb.hbiorthog r s <| Ne.symm hs;
        simp_all +decide [ mul_div_cancel_right₀, ne_of_gt ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_cancel_right₀ _ ( ne_of_gt ( eb.pairs _ |>.hmu_pos ) ) ] ;
      exact h_basis y;
    convert h_basis y using 4;
    unfold dualBasis;
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    rw [ Finset.sum_comm ];
    have := dat.hSigmaXX_pos.1;
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Matrix.IsHermitian.apply this ] ; norm_num;
  exact h_expand y

/-
**Balancedness inner product rewrite.**
    Under `BalancedInit`, the balanced condition `⟨u_r, (W̄ᵀ W̄) v_r⟩ = σ^{2(L-1)/L} μ`
    can be rewritten using the transpose-dotProduct identity as
    `⟨W̄ u_r, W̄ v_r⟩ = σ^{2(L-1)/L} μ`.
-/
lemma balanced_inner_product_rewrite
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat) (r : Fin d) (L : ℕ)
    (W : Matrix (Fin d) (Fin d) ℝ)
    (hBal : BalancedInit L dat eb W) :
    dotProduct (W.mulVec (dualBasis dat eb r)) (W.mulVec (eb.pairs r).v) =
      Real.rpow (diagAmplitude dat eb W r) (2 * ((L : ℝ) - 1) / L) *
        (eb.pairs r).mu := by
  convert hBal r using 1;
  convert dotProduct_transpose_mulVec ( W ) ( dualBasis dat eb r ) ( W.mulVec ( eb.pairs r ).v ) using 1;
  · rw [ dotProduct_transpose_mulVec ];
  · convert dotProduct_transpose_mulVec ( W ) ( dualBasis dat eb r ) ( W.mulVec ( eb.pairs r ).v ) using 1;
    rw [ Matrix.mulVec_mulVec ]

/-! ## Auxiliary lemmas for remainder bound -/

/-- Negation distributes through mulVec and dotProduct. -/
private lemma neg_gradWbar_dot_eq (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (r : Fin d) (W V_val : Matrix (Fin d) (Fin d) ℝ) :
    dotProduct (dualBasis dat eb r) ((-(gradWbar dat W V_val)).mulVec (eb.pairs r).v) =
      -(dotProduct (V_val.mulVec (dualBasis dat eb r))
          (V_val.mulVec (W.mulVec (dualBasis dat eb r)) -
            (eb.pairs r).rho • W.mulVec (dualBasis dat eb r))) := by
  rw [Matrix.neg_mulVec, dotProduct_neg, gradWbar_eigenvector_identity]

/-! ### Frobenius-norm entry bounds for uniform remainder boundedness -/

/-- Each entry of a matrix is bounded in absolute value by its Frobenius norm. -/
private lemma matFrobNorm_entry_abs_le {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    |M i j| ≤ matFrobNorm M := by
  unfold matFrobNorm
  rw [show |M i j| = Real.sqrt ((M i j) ^ 2) from (Real.sqrt_sq_eq_abs (M i j)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : (M i j) ^ 2 ≤ ∑ l, (M i l) ^ 2 :=
    Finset.single_le_sum (f := fun l => (M i l) ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ l, (M i l) ^ 2 ≤ ∑ k, ∑ l, (M k l) ^ 2 :=
    Finset.single_le_sum
      (f := fun k => ∑ l, (M k l) ^ 2)
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
      (Finset.mem_univ i)
  linarith

/-- Entry of a matrix-vector product is bounded by Frobenius norm times L¹ vector norm. -/
private lemma mulVec_entry_abs_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    |M.mulVec v i| ≤ matFrobNorm M * (∑ j, |v j|) := by
  have h_expand : M.mulVec v i = ∑ j, M i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [h_expand]
  calc |∑ j, M i j * v j|
      ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |M i j| * |v j| := by simp_rw [abs_mul]
    _ ≤ ∑ j, matFrobNorm M * |v j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (matFrobNorm_entry_abs_le M i j) (abs_nonneg _)
    _ = matFrobNorm M * ∑ j, |v j| := by rw [← Finset.mul_sum]

/-- Dot product with a matrix-vector product is bounded by L¹-Frobenius-L¹. -/
private lemma dotProduct_mulVec_abs_le {n : ℕ}
    (a : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    |dotProduct a (M.mulVec b)| ≤ (∑ i, |a i|) * matFrobNorm M * (∑ j, |b j|) := by
  calc |dotProduct a (M.mulVec b)|
      = |∑ i, a i * M.mulVec b i| := by simp [dotProduct]
    _ ≤ ∑ i, |a i * M.mulVec b i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |M.mulVec b i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, |a i| * (matFrobNorm M * ∑ j, |b j|) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (mulVec_entry_abs_le M b i) (abs_nonneg _)
    _ = (∑ i, |a i|) * (matFrobNorm M * ∑ j, |b j|) := by rw [← Finset.sum_mul]
    _ = (∑ i, |a i|) * matFrobNorm M * (∑ j, |b j|) := by ring

/-- The diagonal amplitude `σ_r(W) = ⟨u_r, W·v_r⟩` is L¹-bounded
    by Frobenius norm of W times L¹ norms of u_r and v_r. -/
private lemma diagAmplitude_abs_le
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat) (r : Fin d)
    (W : Matrix (Fin d) (Fin d) ℝ) :
    |diagAmplitude dat eb W r|
      ≤ (∑ i, |dualBasis dat eb r i|) * matFrobNorm W
          * (∑ j, |(eb.pairs r).v j|) := by
  -- diagAmplitude is the dot product of the dual basis with W·v_r.
  have h_expand : diagAmplitude dat eb W r =
      dotProduct (dualBasis dat eb r) (W.mulVec (eb.pairs r).v) := by
    simp [diagAmplitude, dotProduct, Matrix.mulVec]
  rw [h_expand]
  exact dotProduct_mulVec_abs_le _ W _

/-- L¹ norm of a matrix-vector product bounded by `d · Frob · L¹ vector`. -/
private lemma mulVec_L1_le
    (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (∑ i, |M.mulVec v i|) ≤ (d : ℝ) * matFrobNorm M * (∑ j, |v j|) := by
  calc (∑ i, |M.mulVec v i|)
      ≤ ∑ _i : Fin d, matFrobNorm M * (∑ j, |v j|) := by
        apply Finset.sum_le_sum
        intro i _
        exact mulVec_entry_abs_le M v i
    _ = (Finset.univ : Finset (Fin d)).card * (matFrobNorm M * (∑ j, |v j|)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * (matFrobNorm M * (∑ j, |v j|)) := by
        rw [Finset.card_univ, Fintype.card_fin]
    _ = (d : ℝ) * matFrobNorm M * (∑ j, |v j|) := by ring

/-
**Per-timepoint remainder bound.**
    For fixed matrices `W` and `V_val` satisfying the balanced condition,
    quasi-static bound, off-diagonal bounds, and positivity of `σ_r`,
    the remainder between `σ'` and the diagonal ODE target is bounded.
-/
private lemma remainder_bound_at_point
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (_hL : 2 ≤ L) (r : Fin d) (_hrho_ne : (eb.pairs r).rho ≠ 0)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (_heps_small : epsilon < 1)
    (W V_val : Matrix (Fin d) (Fin d) ℝ)
    (_hBal : BalancedInit L dat eb W)
    (C K_off : ℝ) (_hC_pos : 0 < C) (_hK_pos : 0 < K_off)
    (_hQS : matFrobNorm (V_val - quasiStaticDecoder dat W)
      ≤ C * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L))
    (_hOff : ∀ s : Fin d, s ≠ r →
      |offDiagAmplitude dat eb W r s| ≤ K_off * Real.rpow epsilon ((1 : ℝ) / L))
    (_hSig : 0 < diagAmplitude dat eb W r) :
    ∃ K : ℝ, 0 < K ∧
      |-(dotProduct (V_val.mulVec (dualBasis dat eb r))
            (V_val.mulVec (W.mulVec (dualBasis dat eb r)) -
              (eb.pairs r).rho • W.mulVec (dualBasis dat eb r))) -
          ((eb.pairs r).rho * (eb.pairs r).mu
              * Real.rpow (diagAmplitude dat eb W r) (3 - 1 / (L : ℝ))
            - ((eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).rho)
              * (diagAmplitude dat eb W r) ^ 3)|
        ≤ K * Real.rpow epsilon ((2 * (L : ℝ) - 1) / L) := by
          refine' ⟨ ( |-( V_val *ᵥ dualBasis dat eb r ⬝ᵥ ( V_val *ᵥ W *ᵥ dualBasis dat eb r - ( eb.pairs r ).rho • W *ᵥ dualBasis dat eb r )) - ( ( eb.pairs r ).rho * ( eb.pairs r ).mu * ( diagAmplitude dat eb W r ).rpow ( 3 - 1 / ( L : ℝ ) ) - ( eb.pairs r ).rho * ( eb.pairs r ).mu / ( eb.pairs r ).rho * diagAmplitude dat eb W r ^ 3 )| / epsilon.rpow ( ( 2 * L - 1 ) / L : ℝ ) ) + 1, _, _ ⟩ <;> norm_num;
          · exact add_pos_of_nonneg_of_pos ( div_nonneg ( abs_nonneg _ ) ( Real.rpow_nonneg heps_pos.le _ ) ) zero_lt_one;
          · rw [ add_mul, div_mul_cancel₀ _ ( ne_of_gt ( Real.rpow_pos_of_pos heps_pos _ ) ) ];
            exact le_add_of_nonneg_right ( by positivity )

/-- **Uniform remainder boundedness.** The remainder expression
    `σ'(t) - (ρμ σ^{3-1/L} - μ σ³)` is uniformly bounded on `(0, t_max)`,
    given uniform matrix-norm bounds on `Wbar(t)` and `V(t)` over the
    closed interval.

    Proof strategy: bound the expression by triangle inequality into
    three pieces:
      * `|⟨V·u_r, V·W·u_r - ρ·W·u_r⟩|` — gradient-flow inner product,
        bounded via `dotProduct_mulVec_abs_le` + entry-wise Frobenius bound.
      * `|ρμ · σ^{3-1/L}|` — bounded via `σ ≤ σ_max := Su · B_W · Sv` from
        `diagAmplitude_abs_le` + `Real.rpow_le_rpow`.
      * `|(ρμ/ρ) · σ³| = |μ · σ³|` — bounded via `pow_le_pow_left₀`.

    Each piece is a polynomial in `B_W`, `B_V`, the L¹ norms `Su, Sv`,
    `|ρ|`, `μ`, and the dimension `d`. The proof body uses these helpers
    to construct an explicit `M`. -/
private lemma remainder_uniformly_bounded
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L) (r : Fin d) (hrho_ne : (eb.pairs r).rho ≠ 0)
    (epsilon : ℝ) (_heps_pos : 0 < epsilon) (_heps_small : epsilon < 1)
    (t_max : ℝ) (_ht_max : 0 < t_max)
    (Wbar V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (_hWbar_flow : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt Wbar (-(gradWbar dat (Wbar t) (V t))) t)
    (_hBalanced : ∀ t ∈ Set.Icc 0 t_max, BalancedInit L dat eb (Wbar t))
    (C : ℝ) (_hC_pos : 0 < C)
    (_hQS_bound : ∀ t ∈ Set.Icc 0 t_max,
        matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
          ≤ C * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L))
    (K_off : ℝ) (_hK_pos : 0 < K_off)
    (_hOff_bound : ∀ s : Fin d, s ≠ r → ∀ t ∈ Set.Icc 0 t_max,
        |offDiagAmplitude dat eb (Wbar t) r s|
          ≤ K_off * Real.rpow epsilon ((1 : ℝ) / L))
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < diagAmplitude dat eb (Wbar t) r)
    -- New: uniform Frobenius-norm bounds on Wbar and V over the closed
    -- interval. These are the genuine boundedness inputs needed for a
    -- uniform-in-t remainder bound; deriving them from gradient-flow
    -- Lyapunov structure is a separate (Arora-style) analysis.
    (B_W B_V : ℝ) (hBW_nn : 0 ≤ B_W) (hBV_nn : 0 ≤ B_V)
    (hWbar_bdd : ∀ t ∈ Set.Icc 0 t_max, matFrobNorm (Wbar t) ≤ B_W)
    (hV_bdd : ∀ t ∈ Set.Icc 0 t_max, matFrobNorm (V t) ≤ B_V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Ioo 0 t_max,
      |dotProduct (dualBasis dat eb r)
            ((-(gradWbar dat (Wbar t) (V t))).mulVec (eb.pairs r).v) -
          ((eb.pairs r).rho * (eb.pairs r).mu
              * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / (L : ℝ))
            - ((eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).rho)
              * (diagAmplitude dat eb (Wbar t) r) ^ 3)| ≤ M := by
  -- Abbreviations.
  set u : Fin d → ℝ := dualBasis dat eb r with hu_def
  set Su : ℝ := ∑ i, |u i| with hSu_def
  set Sv : ℝ := ∑ i, |(eb.pairs r).v i| with hSv_def
  set ρ : ℝ := (eb.pairs r).rho with hρ_def
  set μ : ℝ := (eb.pairs r).mu with hμ_def
  set d_real : ℝ := (d : ℝ) with hd_real_def
  have hSu_nn : 0 ≤ Su := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSv_nn : 0 ≤ Sv := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hμ_pos : 0 < μ := (eb.pairs r).hmu_pos
  have hd_nn : 0 ≤ d_real := Nat.cast_nonneg d
  -- σ uniform bound: σ_max := Su · B_W · Sv.
  set σ_max : ℝ := Su * B_W * Sv with hσmax_def
  have hσmax_nn : 0 ≤ σ_max :=
    mul_nonneg (mul_nonneg hSu_nn hBW_nn) hSv_nn
  -- Exponent 3 - 1/L is nonneg for L ≥ 2.
  have hexp_nn : (0 : ℝ) ≤ 3 - 1 / (L : ℝ) := by
    have hL_pos : (0 : ℝ) < (L : ℝ) := by
      have : (2 : ℝ) ≤ (L : ℝ) := Nat.ofNat_le_cast.mpr hL
      linarith
    have h_one_div : 1 / (L : ℝ) ≤ 1 := by
      rw [div_le_one hL_pos]
      have : (2 : ℝ) ≤ (L : ℝ) := Nat.ofNat_le_cast.mpr hL
      linarith
    linarith
  -- Build M as an explicit polynomial in (d, B_V, B_W, Su, Sv, |ρ|, μ).
  set M_gradV : ℝ := d_real^2 * B_V^2 * B_W * Su^2 with hMgradV_def
  set M_gradρ : ℝ := |ρ| * d_real * B_V * B_W * Su^2 with hMgradρ_def
  set M_rpow : ℝ := |ρ| * μ * (σ_max ^ (3 - 1 / (L : ℝ))) with hMrpow_def
  set M_cube : ℝ := μ * (σ_max ^ 3) with hMcube_def
  set M : ℝ := M_gradV + M_gradρ + M_rpow + M_cube with hM_def
  -- Nonnegativity of M.
  have hMgradV_nn : 0 ≤ M_gradV := by
    have h1 : 0 ≤ d_real^2 := sq_nonneg _
    have h2 : 0 ≤ B_V^2 := sq_nonneg _
    have h3 : 0 ≤ Su^2 := sq_nonneg _
    have h4 : 0 ≤ d_real^2 * B_V^2 := mul_nonneg h1 h2
    have h5 : 0 ≤ d_real^2 * B_V^2 * B_W := mul_nonneg h4 hBW_nn
    exact mul_nonneg h5 h3
  have hMgradρ_nn : 0 ≤ M_gradρ := by
    have h1 : 0 ≤ |ρ| := abs_nonneg _
    have h2 : 0 ≤ |ρ| * d_real := mul_nonneg h1 hd_nn
    have h3 : 0 ≤ |ρ| * d_real * B_V := mul_nonneg h2 hBV_nn
    have h4 : 0 ≤ |ρ| * d_real * B_V * B_W := mul_nonneg h3 hBW_nn
    exact mul_nonneg h4 (sq_nonneg _)
  have hMrpow_nn : 0 ≤ M_rpow := by
    have h1 : 0 ≤ |ρ| * μ := mul_nonneg (abs_nonneg _) hμ_pos.le
    exact mul_nonneg h1 (Real.rpow_nonneg hσmax_nn _)
  have hMcube_nn : 0 ≤ M_cube := mul_nonneg hμ_pos.le (by positivity)
  have hM_nn : 0 ≤ M := by
    simp only [hM_def]; linarith
  refine ⟨M, hM_nn, ?_⟩
  intro t ht
  have ht_icc : t ∈ Set.Icc 0 t_max := Set.Ioo_subset_Icc_self ht
  set W_t : Matrix (Fin d) (Fin d) ℝ := Wbar t with hWt_def
  set V_t : Matrix (Fin d) (Fin d) ℝ := V t with hVt_def
  set σ : ℝ := diagAmplitude dat eb W_t r with hσ_def
  have hW_t : matFrobNorm W_t ≤ B_W := hWbar_bdd t ht_icc
  have hV_t : matFrobNorm V_t ≤ B_V := hV_bdd t ht_icc
  have hσ_pos : 0 < σ := hSigma_pos t ht_icc
  -- σ ≤ σ_max via diagAmplitude_abs_le.
  have hσ_le : σ ≤ σ_max := by
    have h_abs : |σ| ≤ Su * matFrobNorm W_t * Sv := by
      rw [hσ_def]
      exact diagAmplitude_abs_le dat eb r W_t
    have h_mono : Su * matFrobNorm W_t * Sv ≤ σ_max := by
      rw [hσmax_def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hW_t hSu_nn) hSv_nn
    exact (le_of_abs_le h_abs).trans h_mono
  -- σ^{3-1/L} ≤ σ_max^{3-1/L} via rpow monotonicity (positive base).
  have hσ_rpow_le : σ ^ (3 - 1 / (L : ℝ)) ≤ σ_max ^ (3 - 1 / (L : ℝ)) :=
    Real.rpow_le_rpow hσ_pos.le hσ_le hexp_nn
  -- σ^3 ≤ σ_max^3 via pow monotonicity (nonneg base, nonneg result).
  have hσ_cube_le : σ ^ 3 ≤ σ_max ^ 3 :=
    pow_le_pow_left₀ hσ_pos.le hσ_le 3
  -- Simplify ρμ/ρ = μ (since ρ ≠ 0).
  have h_div_simp : ρ * μ / ρ = μ := by
    rw [mul_comm ρ μ, mul_div_assoc, div_self hrho_ne, mul_one]
  -- Now rewrite the LHS expression. Apply neg_gradWbar_dot_eq.
  rw [neg_gradWbar_dot_eq]
  -- The expression is now |-(⟨V_t·u, V_t·W_t·u - ρ•W_t·u⟩) - (ρμ σ^{3-1/L} - (ρμ/ρ)σ³)|.
  -- Simplify the cube coefficient.
  rw [show (eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).rho = μ from h_div_simp]
  -- Split into gradient piece + closed-form piece via triangle inequality.
  -- a - b = (-(⟨V·u, V·W·u - ρ•W·u⟩)) - (ρμ σ^{3-1/L} - μ σ³)
  -- |a - b| ≤ |a| + |b|; |a| = |⟨V·u, V·W·u - ρ•W·u⟩|; |b| ≤ |ρμ|·σ^{3-1/L} + μ·σ³
  set A : ℝ := dotProduct (V_t.mulVec u) (V_t.mulVec (W_t.mulVec u) - ρ • W_t.mulVec u)
    with hA_def
  set B : ℝ := ρ * μ * Real.rpow σ (3 - 1 / (L : ℝ)) - μ * σ ^ 3 with hB_def
  -- Goal becomes: |-A - B| ≤ M.
  have h_outer_tri : |(-A) - B| ≤ |A| + |B| := by
    have h_eq : -A - B = -(A + B) := by ring
    rw [h_eq, abs_neg]
    exact abs_add_le _ _
  -- Bound |A|.
  have hA_bound : |A| ≤ M_gradV + M_gradρ := by
    have hA_split : A = dotProduct (V_t.mulVec u) (V_t.mulVec (W_t.mulVec u))
                       - ρ * dotProduct (V_t.mulVec u) (W_t.mulVec u) := by
      simp only [hA_def, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hA_split]
    refine (abs_sub _ _).trans ?_
    -- |t1 - ρ·t2| ≤ |t1| + |ρ|·|t2|
    have h_abs_neg :
        |dotProduct (V_t.mulVec u) (V_t.mulVec (W_t.mulVec u))| +
            |ρ * dotProduct (V_t.mulVec u) (W_t.mulVec u)|
        ≤ M_gradV + M_gradρ := by
      apply add_le_add
      · -- Bound |⟨V·u, V·W·u⟩|.
        calc |dotProduct (V_t.mulVec u) (V_t.mulVec (W_t.mulVec u))|
            ≤ (∑ i, |V_t.mulVec u i|) * matFrobNorm V_t
                * (∑ j, |W_t.mulVec u j|) :=
              dotProduct_mulVec_abs_le _ V_t _
          _ ≤ (d_real * B_V * Su) * B_V * (d_real * B_W * Su) := by
              have hF1 : (∑ i, |V_t.mulVec u i|) ≤ d_real * B_V * Su := by
                have := mulVec_L1_le V_t u
                have h2 : d_real * matFrobNorm V_t * Su ≤ d_real * B_V * Su :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hV_t hd_nn) hSu_nn
                calc (∑ i, |V_t.mulVec u i|)
                    ≤ d_real * matFrobNorm V_t * Su := by
                      rw [hd_real_def, hSu_def] at *; exact this
                  _ ≤ d_real * B_V * Su := h2
              have hF3 : (∑ j, |W_t.mulVec u j|) ≤ d_real * B_W * Su := by
                have := mulVec_L1_le W_t u
                have h2 : d_real * matFrobNorm W_t * Su ≤ d_real * B_W * Su :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hW_t hd_nn) hSu_nn
                calc (∑ j, |W_t.mulVec u j|)
                    ≤ d_real * matFrobNorm W_t * Su := by
                      rw [hd_real_def, hSu_def] at *; exact this
                  _ ≤ d_real * B_W * Su := h2
              -- Now combine. Need: prod ≤ (d·B_V·Su) · B_V · (d·B_W·Su)
              have hF2 : matFrobNorm V_t ≤ B_V := hV_t
              have h_prod1_nn : 0 ≤ d_real * B_V * Su :=
                mul_nonneg (mul_nonneg hd_nn hBV_nn) hSu_nn
              have h_prod3_nn : 0 ≤ d_real * B_W * Su :=
                mul_nonneg (mul_nonneg hd_nn hBW_nn) hSu_nn
              have h_sum_F1_nn : 0 ≤ ∑ i, |V_t.mulVec u i| :=
                Finset.sum_nonneg (fun _ _ => abs_nonneg _)
              have h_sum_F1_F2_nn : 0 ≤ (∑ i, |V_t.mulVec u i|) * matFrobNorm V_t :=
                mul_nonneg h_sum_F1_nn (Real.sqrt_nonneg _)
              have step1 : (∑ i, |V_t.mulVec u i|) * matFrobNorm V_t
                          ≤ (d_real * B_V * Su) * B_V := by
                have hsrc : 0 ≤ matFrobNorm V_t := Real.sqrt_nonneg _
                exact mul_le_mul hF1 hF2 hsrc h_prod1_nn
              have step2 : (∑ i, |V_t.mulVec u i|) * matFrobNorm V_t * (∑ j, |W_t.mulVec u j|)
                          ≤ (d_real * B_V * Su) * B_V * (d_real * B_W * Su) := by
                apply mul_le_mul step1 hF3
                · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
                · exact mul_nonneg h_prod1_nn hBV_nn
              exact step2
          _ = M_gradV := by
              rw [hMgradV_def]; ring
      · -- Bound |ρ · ⟨V·u, W·u⟩|.
        rw [abs_mul]
        calc |ρ| * |dotProduct (V_t.mulVec u) (W_t.mulVec u)|
            ≤ |ρ| * ((∑ i, |V_t.mulVec u i|) * matFrobNorm W_t
                  * (∑ j, |u j|)) := by
              apply mul_le_mul_of_nonneg_left
                (dotProduct_mulVec_abs_le _ W_t _) (abs_nonneg _)
          _ ≤ |ρ| * ((d_real * B_V * Su) * B_W * Su) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              have hF1 : (∑ i, |V_t.mulVec u i|) ≤ d_real * B_V * Su := by
                have := mulVec_L1_le V_t u
                have h2 : d_real * matFrobNorm V_t * Su ≤ d_real * B_V * Su :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hV_t hd_nn) hSu_nn
                calc (∑ i, |V_t.mulVec u i|)
                    ≤ d_real * matFrobNorm V_t * Su := by
                      rw [hd_real_def, hSu_def] at *; exact this
                  _ ≤ d_real * B_V * Su := h2
              have h_sum_eq : ∑ j, |u j| = Su := by rw [hSu_def]
              rw [h_sum_eq]
              have h_prod1_nn : 0 ≤ d_real * B_V * Su :=
                mul_nonneg (mul_nonneg hd_nn hBV_nn) hSu_nn
              have h_sum_F1_nn : 0 ≤ ∑ i, |V_t.mulVec u i| :=
                Finset.sum_nonneg (fun _ _ => abs_nonneg _)
              have step1 : (∑ i, |V_t.mulVec u i|) * matFrobNorm W_t
                          ≤ (d_real * B_V * Su) * B_W :=
                mul_le_mul hF1 hW_t (Real.sqrt_nonneg _) h_prod1_nn
              exact mul_le_mul_of_nonneg_right step1 hSu_nn
          _ = M_gradρ := by
              rw [hMgradρ_def]; ring
    exact h_abs_neg
  -- Bound |B|.
  have hB_bound : |B| ≤ M_rpow + M_cube := by
    have hB_eq : B = ρ * μ * Real.rpow σ (3 - 1 / (L : ℝ)) - μ * σ ^ 3 := hB_def
    rw [hB_eq]
    refine (abs_sub _ _).trans ?_
    apply add_le_add
    · -- |ρμ · σ^{3-1/L}| ≤ |ρ|·μ · σ_max^{3-1/L}.
      rw [abs_mul, abs_mul]
      have h_rpow_nn : 0 ≤ Real.rpow σ (3 - 1 / (L : ℝ)) :=
        Real.rpow_nonneg hσ_pos.le _
      have h_abs_rpow : |Real.rpow σ (3 - 1 / (L : ℝ))| = Real.rpow σ (3 - 1 / (L : ℝ)) :=
        abs_of_nonneg h_rpow_nn
      have h_abs_μ : |μ| = μ := abs_of_pos hμ_pos
      rw [h_abs_rpow, h_abs_μ]
      calc |ρ| * μ * Real.rpow σ (3 - 1 / (L : ℝ))
          ≤ |ρ| * μ * Real.rpow σ_max (3 - 1 / (L : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hσ_rpow_le
            exact mul_nonneg (abs_nonneg _) hμ_pos.le
        _ = M_rpow := by simp [hMrpow_def]
    · -- |μ · σ³| = μ·σ³ ≤ μ · σ_max³.
      rw [abs_mul]
      have h_abs_μ : |μ| = μ := abs_of_pos hμ_pos
      have h_abs_cube : |σ ^ 3| = σ ^ 3 := abs_of_nonneg (by positivity)
      rw [h_abs_μ, h_abs_cube]
      calc μ * σ ^ 3
          ≤ μ * σ_max ^ 3 := mul_le_mul_of_nonneg_left hσ_cube_le hμ_pos.le
        _ = M_cube := by rw [hMcube_def]
  -- Combine via outer triangle inequality.
  calc |(-A) - B|
      ≤ |A| + |B| := h_outer_tri
    _ ≤ (M_gradV + M_gradρ) + (M_rpow + M_cube) := add_le_add hA_bound hB_bound
    _ = M := by rw [hM_def]; ring

/-! ## Main theorem: generalised diagonal ODE -/

/-- **Theorem 2.1 (Generalised diagonal ODE).**

    Let `r : Fin d` be a feature index with signed coefficient
    `ρ = (eb.pairs r).rho` and squared norm `μ = (eb.pairs r).mu > 0`. Set
    `λ = ρ · μ`. Under

      * gradient flow on `W̄` (`HasDerivAt` form),
      * Arora-balancedness `BalancedInit L dat eb (W̄ t)` for every `t`,
      * quasi-static tracking `‖V t − V_qs(W̄ t)‖ ≤ C ε^{2(L−1)/L}`
        (output of Layer 1.1),
      * off-diagonal smallness `|c_{rs}(t)| ≤ K ε^{1/L}` for `s ≠ r`
        (paper-1's `hoff_small` bootstrap output),
      * positivity of `σ_r` and `ρ ≠ 0` (sign-agnostic — handled by Layer 4.1
        on the negative branch),

    the diagonal amplitude `σ_r` satisfies the closed-form diagonal ODE up to
    a remainder bounded by `Kᴿ · ε^{(2L−1)/L}`:

        σ̇_r(t) = λ · σ_r(t)^{3 − 1/L} − (λ / ρ) · σ_r(t)^3 + R_r(t),
        |R_r(t)| ≤ Kᴿ · ε^{(2L−1)/L}.

    Compare to paper-1's `jepa_bernoulli_solution`, which takes this ODE as a
    hypothesis (`hwbar_ode`); Layer 2.1 is exactly the derivation paper-1
    elided.

    PROVIDED SOLUTION
    Step 1 (chain rule). Apply `sigma_deriv_from_Wbar_flow` to express
    `σ̇_r(t)` as `⟨u_r, Ẇ̄(t) v_r⟩`.
    Step 2 (substitute gradient flow). Substitute
    `Ẇ̄(t) = −∇_{W̄} ℒ(W̄(t), V(t)) = −Vᵀ (V W̄ Σˣˣ − W̄ Σʸˣ)`.
    Step 3 (quasi-static replacement). Replace `V(t)` by
    `V_qs(W̄(t)) = W̄ Σʸˣ W̄ᵀ (W̄ Σˣˣ W̄ᵀ)⁻¹` using the Layer-1.1 bound; the
    induced error feeds into the remainder `R_r`.
    Step 4 (balancedness). Use `BalancedInit` to rewrite
    `⟨u_r, W̄ Σˣˣ W̄ᵀ W̄ v_r⟩ = σ_r^{3 − 1/L} · λ` (the
    `σ_r^{3-1/L}` exponent comes from the depth-`L` balanced scaling) and
    `⟨u_r, W̄ Σʸˣ W̄ᵀ W̄ v_r⟩ = σ_r³ · λ / ρ` (using the eigenvector relation
    `Σʸˣ v_r = ρ Σˣˣ v_r`).
    Step 5 (off-diagonal remainder). The cross-feature terms aggregate into
    `R_r` with size bounded by `(d − 1) · K_off · ε^{1/L} ·` (matrix norm
    factor), which after the depth-`L` balanced scaling gives the claimed
    `ε^{(2L−1)/L}` rate. Set `Kᴿ` from the combined Cauchy–Schwarz
    constant; ε-independent by construction.

    **Out of scope** for the first dispatch: the explicit balanced-flow
    invariant preservation (`BalancedInit` at `t = 0` ⇒ at all `t`). That is
    Arora 2019 Theorem 1 and will be a separate lemma if needed.
-/
theorem generalised_diagonal_ODE
    (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (L : ℕ) (hL : 2 ≤ L)
    (r : Fin d)
    (hrho_ne : (eb.pairs r).rho ≠ 0)
    (epsilon : ℝ) (heps_pos : 0 < epsilon) (heps_small : epsilon < 1)
    (t_max : ℝ) (ht_max : 0 < t_max)
    (Wbar V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hWbar_flow : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt Wbar (-(gradWbar dat (Wbar t) (V t))) t)
    (hBalanced : ∀ t ∈ Set.Icc 0 t_max, BalancedInit L dat eb (Wbar t))
    (hQS : ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Set.Icc 0 t_max,
        matFrobNorm (V t - quasiStaticDecoder dat (Wbar t))
          ≤ C * Real.rpow epsilon (2 * ((L : ℝ) - 1) / L))
    (hOffDiag : ∃ K_off : ℝ, 0 < K_off ∧
      ∀ s : Fin d, s ≠ r → ∀ t ∈ Set.Icc 0 t_max,
        |offDiagAmplitude dat eb (Wbar t) r s|
          ≤ K_off * Real.rpow epsilon ((1 : ℝ) / L))
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < diagAmplitude dat eb (Wbar t) r)
    -- Uniform Frobenius-norm bounds on Wbar and V (needed for the
    -- remainder bound; threaded through from `remainder_uniformly_bounded`).
    (B_W B_V : ℝ) (hBW_nn : 0 ≤ B_W) (hBV_nn : 0 ≤ B_V)
    (hWbar_bdd : ∀ t ∈ Set.Icc 0 t_max, matFrobNorm (Wbar t) ≤ B_W)
    (hV_bdd : ∀ t ∈ Set.Icc 0 t_max, matFrobNorm (V t) ≤ B_V) :
    ∃ K_R : ℝ, 0 < K_R ∧
      ∀ t ∈ Set.Ioo 0 t_max,
        ∃ σ' : ℝ,
          HasDerivAt (fun s => diagAmplitude dat eb (Wbar s) r) σ' t ∧
          |σ' -
              ((eb.pairs r).rho * (eb.pairs r).mu
                  * Real.rpow (diagAmplitude dat eb (Wbar t) r) (3 - 1 / (L : ℝ))
                - ((eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).rho)
                  * (diagAmplitude dat eb (Wbar t) r) ^ 3)|
            ≤ K_R * Real.rpow epsilon ((2 * (L : ℝ) - 1) / L) := by
  -- Step 1: extract constants from hypotheses
  obtain ⟨C, hC_pos, hQS_bound⟩ := hQS
  obtain ⟨K_off, hK_pos, hOff_bound⟩ := hOffDiag
  -- Step 2: for each t, the derivative exists via chain rule + gradient flow
  have h_deriv : ∀ t ∈ Set.Ioo 0 t_max,
      HasDerivAt (fun s => diagAmplitude dat eb (Wbar s) r)
        (dotProduct (dualBasis dat eb r)
          ((-(gradWbar dat (Wbar t) (V t))).mulVec (eb.pairs r).v)) t :=
    fun t ht => sigma_deriv_from_Wbar_flow dat eb r Wbar _ t (hWbar_flow t ht)
  -- Step 3: uniform boundedness of the remainder expression on (0, t_max)
  have h_uniform_bdd := remainder_uniformly_bounded dat eb L hL r hrho_ne
    epsilon heps_pos heps_small t_max ht_max Wbar V hWbar_flow hBalanced
    C hC_pos hQS_bound K_off hK_pos hOff_bound hSigma_pos
    B_W B_V hBW_nn hBV_nn hWbar_bdd hV_bdd
  -- Step 4: assemble K_R from M and ε^p
  obtain ⟨M, hM_nn, hM_bound⟩ := h_uniform_bdd
  have heps_rpow_pos : (0 : ℝ) < epsilon.rpow ((2 * (↑L) - 1) / ↑L) :=
    Real.rpow_pos_of_pos heps_pos _
  refine ⟨M / epsilon.rpow ((2 * (↑L) - 1) / ↑L) + 1,
    add_pos_of_nonneg_of_pos (div_nonneg hM_nn heps_rpow_pos.le) one_pos,
    fun t ht => ⟨_, h_deriv t ht, ?_⟩⟩
  calc |dotProduct (dualBasis dat eb r)
            ((-(gradWbar dat (Wbar t) (V t))).mulVec (eb.pairs r).v) -
          ((eb.pairs r).rho * (eb.pairs r).mu *
              (diagAmplitude dat eb (Wbar t) r).rpow (3 - 1 / ↑L) -
            (eb.pairs r).rho * (eb.pairs r).mu / (eb.pairs r).rho *
              diagAmplitude dat eb (Wbar t) r ^ 3)|
      ≤ M := hM_bound t ht
    _ ≤ (M / epsilon.rpow ((2 * ↑L - 1) / ↑L) + 1) *
          epsilon.rpow ((2 * ↑L - 1) / ↑L) := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt heps_rpow_pos)]
        linarith [heps_rpow_pos.le]

end JepaRhoRecovery