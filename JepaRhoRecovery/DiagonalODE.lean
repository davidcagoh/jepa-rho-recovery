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
    (hSigma_pos : ∀ t ∈ Set.Icc 0 t_max, 0 < diagAmplitude dat eb (Wbar t) r) :
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
  -- Step 3: define the remainder function
  -- For each t, σ'(t) is the derivative and target(t) is the ODE right-hand side
  -- R(t) = σ'(t) - target(t)
  -- We use the identity: σ'(t) = -(bilinear form from gradWbar_eigenvector_identity)
  -- The bound |R(t)| ≤ K_R * ε^{(2L-1)/L} follows from the hypotheses
  -- Step 4: assemble the existential
  -- K_R is chosen large enough (can depend on ε, Wbar, V, everything)
  -- The remainder bound follows from hQS, hOffDiag, and hBalanced
  sorry

end JepaRhoRecovery