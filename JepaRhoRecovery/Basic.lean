/-
# JepaRhoRecovery.Basic

Core definitions for the ρ*-recovery extension. **Signed-first design**: all
structures admit signed ρ* from the start. The positive-only specialisation
is a derived predicate (`0 < pair.rho`), never a structure axiom.

Ports definitions from `../jepa-learning-order/JepaLearningOrder/JEPA.lean`
with the positivity hypothesis removed. See `paper/outline.md` §2 for the
signed setup.
-/

import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped Matrix

namespace JepaRhoRecovery

variable {d : ℕ}

/-- Frobenius norm for matrices. -/
noncomputable def matFrobNorm {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (M i j) ^ 2)

/-! ## Section 2: JEPA model -/

/-- Covariance triple `(Σˣˣ, Σʸˣ, Σʸʸ)` with Σˣˣ positive definite.
    Ported verbatim from `JepaLearningOrder.JEPA.JEPAData`. -/
structure JEPAData (d : ℕ) where
  SigmaXX : Matrix (Fin d) (Fin d) ℝ
  SigmaYX : Matrix (Fin d) (Fin d) ℝ
  SigmaYY : Matrix (Fin d) (Fin d) ℝ
  hSigmaXX_pos : Matrix.PosDef SigmaXX

/-- Regression operator ℛ = (Σˣˣ)⁻¹ Σʸˣ (Definition 2.1). -/
noncomputable def regressionOperator (dat : JEPAData d) : Matrix (Fin d) (Fin d) ℝ :=
  dat.SigmaXX⁻¹ * dat.SigmaYX

/-- JEPA loss ℒ(W̄, V) = ½ tr(V W̄ Σˣˣ W̄ᵀ Vᵀ) - tr(V W̄ Σʸˣ) + ½ tr(W̄ Σʸʸ W̄ᵀ). -/
noncomputable def JEPALoss (dat : JEPAData d)
    (Wbar V : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2) * Matrix.trace (V * Wbar * dat.SigmaXX * Wbarᵀ * Vᵀ)
  - Matrix.trace (V * Wbar * dat.SigmaYX)
  + (1 / 2) * Matrix.trace (Wbar * dat.SigmaYY * Wbarᵀ)

/-- ∇_V ℒ = V W̄ Σˣˣ W̄ᵀ - W̄ Σʸˣ W̄ᵀ (Littwin convention; see paper-1 note). -/
noncomputable def gradV (dat : JEPAData d)
    (Wbar V : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  V * Wbar * dat.SigmaXX * Wbarᵀ - Wbar * dat.SigmaYX * Wbarᵀ

/-- ∇_{W̄} ℒ = Vᵀ (V W̄ Σˣˣ - W̄ Σʸˣ). -/
noncomputable def gradWbar (dat : JEPAData d)
    (Wbar V : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Vᵀ * (V * Wbar * dat.SigmaXX - Wbar * dat.SigmaYX)

/-! ## Section 2: Signed generalised eigenstructure

    This is where we diverge from paper-1: `rho` is signed; positivity is a
    derived predicate, never a structure axiom. -/

/-- Signed generalised eigenpair `(v, ρ, μ)` satisfying Σʸˣ v = ρ Σˣˣ v
    with Σˣˣ-norm squared `μ = vᵀ Σˣˣ v > 0`. The eigenvalue `ρ` is **signed**
    — no `0 < rho` axiom (the whole point of the spinoff). -/
structure SignedGenEigenpair (dat : JEPAData d) where
  v       : Fin d → ℝ
  rho     : ℝ
  mu      : ℝ
  heig    : dat.SigmaYX.mulVec v = rho • dat.SigmaXX.mulVec v
  hmu_pos : 0 < mu
  hmu_def : mu = dotProduct v (dat.SigmaXX.mulVec v)

/-- Signed generalised eigenbasis: `d` signed eigenpairs with strictly
    decreasing (signed) eigenvalues and Σˣˣ-biorthogonality.
    Ordering convention: `pairs 0` is the largest ρ (most positive). -/
structure SignedGenEigenbasis (dat : JEPAData d) where
  pairs : Fin d → SignedGenEigenpair dat
  hstrictly_decreasing : ∀ r s : Fin d, r < s → (pairs s).rho < (pairs r).rho
  hbiorthog : ∀ r s : Fin d, r ≠ s →
    dotProduct (pairs r).v (dat.SigmaXX.mulVec (pairs s).v) = 0

/-- Predicate: an eigenpair has positive ρ. Use this as a hypothesis on
    specific lemmas (positive-branch theorems), never bake it into structures. -/
def SignedGenEigenpair.IsPositive {dat : JEPAData d} (p : SignedGenEigenpair dat) : Prop :=
  0 < p.rho

/-- Predicate: an eigenpair has negative ρ (Layer 4 suppression branch). -/
def SignedGenEigenpair.IsNegative {dat : JEPAData d} (p : SignedGenEigenpair dat) : Prop :=
  p.rho < 0

/-- Dual left basis under the Σˣˣ-inner product. -/
noncomputable def dualBasis (dat : JEPAData d) (eb : SignedGenEigenbasis dat) :
    Fin d → (Fin d → ℝ) :=
  fun r => dat.SigmaXX.mulVec (eb.pairs r).v

/-- Projected covariance λ_r* = ρ_r* · μ_r (signed; sign of λ matches sign of ρ). -/
noncomputable def projectedCovariance (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (r : Fin d) : ℝ :=
  (eb.pairs r).rho * (eb.pairs r).mu

/-- Diagonal amplitude σ_r(t) = u_rᵀ W̄(t) v_r* (Definition 2.3). -/
noncomputable def diagAmplitude (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (Wbar : Matrix (Fin d) (Fin d) ℝ) (r : Fin d) : ℝ :=
  dotProduct (dualBasis dat eb r) (Wbar.mulVec (eb.pairs r).v)

/-- Off-diagonal amplitude c_{rs}(t) = u_rᵀ W̄(t) v_s* for r ≠ s. -/
noncomputable def offDiagAmplitude (dat : JEPAData d) (eb : SignedGenEigenbasis dat)
    (Wbar : Matrix (Fin d) (Fin d) ℝ) (r s : Fin d) : ℝ :=
  dotProduct (dualBasis dat eb r) (Wbar.mulVec (eb.pairs s).v)

/-- Balanced-network preconditioner P_{rs} = Σ_a σ_r^{2(L-a)/L} σ_s^{2(a-1)/L}.
    P_{rr}(σ, σ) = L · σ^{2(L-1)/L}. Uses `Real.rpow` for fractional exponents. -/
noncomputable def preconditioner (L : ℕ) (sigma_r sigma_s : ℝ) : ℝ :=
  ∑ a : Fin L,
    Real.rpow sigma_r (2 * ((L : ℝ) - ((a.val : ℝ) + 1)) / (L : ℝ))
    * Real.rpow sigma_s (2 * (a.val : ℝ) / (L : ℝ))

/-- Quasi-static decoder: V_qs(W̄) = W̄ Σʸˣ W̄ᵀ (W̄ Σˣˣ W̄ᵀ)⁻¹ (Definition 5.1). -/
noncomputable def quasiStaticDecoder (dat : JEPAData d)
    (Wbar : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Wbar * dat.SigmaYX * Wbarᵀ * (Wbar * dat.SigmaXX * Wbarᵀ)⁻¹

end JepaRhoRecovery
