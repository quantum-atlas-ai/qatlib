/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.MatrixUnitFactors

@[expose] public section


/-! # Complete matrix-unit assembly of the physical CKG parent

All `D^2` transition labels and all `D^2` operator coordinates are retained.
Equal Bohr frequencies are allowed: their cross terms remain in the sum.
Proposal labels are summed outside their individual Gram operators, so there
are no cross-proposal terms. The physical factor `1/2` is the one in
`parentGramFamOp`; the optional real kernel is `1` for the plain parent and
`fun nu => 2 * phaseKernel beta nu` for the damped parent.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- Every matrix unit of the original Hilbert space is retained. -/
abbrev FullCoord (D : ℕ) := Fin D × Fin D

/-- Vectorization indexed by the actual row and column, without a hidden
permutation or a projection to a smaller energy subspace. -/
def fullVec (X : Operator D) : FullCoord D → ℂ := fun p => X p.1 p.2

/-- The frequency of the actual matrix unit `E_ij` is `lambda_i-lambda_j`. -/
def fullNu (lam : Fin D → ℝ) (a : FullCoord D) : ℝ := lam a.1 - lam a.2

/-- A proposal's individual spectral transition, including its complex entry. -/
def fullTransition (A : Operator D) (a : FullCoord D) : Operator D :=
  matUnit a.1 a.2 (A a.1 a.2)

/-- Explicit matrix of a single thermal first-order factor. Its row is the
output coordinate and its column the input coordinate; the adjoint below
therefore conjugates the first factor, not the second. -/
noncomputable def fullFactorMatrix (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (a : FullCoord D) : Matrix (FullCoord D) (FullCoord D) ℂ :=
  fun p q => A a.1 a.2 *
    ((if p.1 = a.1 then (Real.exp (-(β * fullNu lam a) / 4) : ℂ)
        * (if a.2 = q.1 ∧ p.2 = q.2 then 1 else 0) else 0)
      - (if p.2 = a.2 then (Real.exp (β * fullNu lam a / 4) : ℂ)
        * (if p.1 = q.1 ∧ a.1 = q.2 then 1 else 0) else 0))

/-- Transported source weight with an explicit optional damping kernel. -/
noncomputable def fullWeight (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (a b : FullCoord D) : ℝ :=
  ckgSourceWeight β (fullNu lam a) (fullNu lam b)
    * kern (fullNu lam a - fullNu lam b)

/-- Actual sum of physical family operators. Each proposal contributes its
own complete transition family, with the physical half inside the library API. -/
noncomputable def fullParentOp (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) : Operator D →ₗ[ℂ] Operator D :=
  ∑ P, parentGramFamOp (fullWeight lam β kern) (gibbsDiag lam β)
    (fullTransition (A P))

/-- Independently assembled full matrix `sum_Pab (w_ab/2) F_Pa^H F_Pb`. -/
noncomputable def fullGramMatrix (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) : Matrix (FullCoord D) (FullCoord D) ℂ :=
  ∑ P, ∑ a, ∑ b, ((fullWeight lam β kern a b / 2 : ℝ) : ℂ) •
    ((fullFactorMatrix lam β (A P) a)ᴴ * fullFactorMatrix lam β (A P) b)

/-- The matrix of an actual complex-linear operator in the complete matrix-unit basis. -/
noncomputable def fullOpMatrix (L : Operator D →ₗ[ℂ] Operator D) :
    Matrix (FullCoord D) (FullCoord D) ℂ :=
  fun p q => L (matUnit q.1 q.2 1) p.1 p.2

/-- The transition family reconstructs the whole proposal, including every
diagonal entry and every repeated-frequency transition. -/
theorem fullTransition_sum (A : Operator D) : ∑ a, fullTransition A a = A := by
  classical
  ext i j
  simp [fullTransition, Fintype.sum_prod_type, Matrix.sum_apply, matUnit_apply, ite_and]

/-- Full Transition eq smul for the stated finite source data. -/
theorem fullTransition_eq_smul (A : Operator D) (a : FullCoord D) :
    fullTransition A a = A a.1 a.2 • matUnit a.1 a.2 1 := by
  ext i j
  simp only [fullTransition, Matrix.smul_apply, smul_eq_mul, matUnit_apply]
  by_cases h : i = a.1 ∧ j = a.2 <;> simp [h]

/-- Each retained transition is a genuine Bohr component of the same
diagonal Hamiltonian, with the source convention `[H,A_nu] = nu A_nu`. -/
theorem fullTransition_bohr (lam : Fin D → ℝ) (A : Operator D) (a : FullCoord D) :
    Matrix.diagonal (fun i => (lam i : ℂ)) * fullTransition A a
      - fullTransition A a * Matrix.diagonal (fun i => (lam i : ℂ)) =
      (fullNu lam a : ℂ) • fullTransition A a := by
  simp only [fullTransition, diagonal_mul_matUnit, matUnit_mul_diagonal,
    fullNu, Complex.ofReal_sub, sub_smul]

/-- The weight used by the complete matrix is exactly the source alpha
weight after its required thermal transport, including the optional kernel. -/
theorem fullWeight_eq_source_transport (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (a b : FullCoord D) :
    fullWeight lam β kern a b =
      ckgWeight β (fullNu lam a) (fullNu lam b)
        * Real.exp (β * (fullNu lam a + fullNu lam b) / 4)
        * kern (fullNu lam a - fullNu lam b) := by
  rw [fullWeight, ckgSourceWeight_eq]

/-- Complete matrix-unit expansion of an arbitrary complex operator. -/
theorem fullMatrixUnit_decomposition (X : Operator D) :
    (∑ q : FullCoord D, X q.1 q.2 • matUnit q.1 q.2 1) = X := by
  classical
  ext i j
  simp [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, matUnit_apply, mul_ite, ite_and]

/-- Matrix-unit coordinates are recovered from the actual Hilbert--Schmidt
inner product, whose first argument is conjugated. -/
theorem fullHsInner_matUnit (p : FullCoord D) (X : Operator D) :
    hsInner (matUnit p.1 p.2 1) X = X p.1 p.2 := by
  simp [hsInner_eq_sum, matUnit_apply, apply_ite, ite_mul, ite_and]

/-- The explicit thermal/delta formula represents the library's physical
`parentFactor` for the actual proposal transition. -/
theorem fullFactorMatrix_eq_parentFactor (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (a p q : FullCoord D) :
    fullFactorMatrix lam β A a p q =
      (parentFactor (gibbsDiag lam β) (fullTransition A a)
        (matUnit q.1 q.2 1)) p.1 p.2 := by
  rw [fullTransition_eq_smul, parentFactor_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, parentFactor_matUnit_entry,
    matUnit_apply, fullFactorMatrix, fullNu]

/-- A complete operator matrix acts on every complex input, not merely on
the matrix units used to construct its columns. -/
theorem fullOpMatrix_mulVec (L : Operator D →ₗ[ℂ] Operator D) (X : Operator D) :
    (fullOpMatrix L).mulVec (fullVec X) = fullVec (L X) := by
  classical
  funext p
  have h := congrArg (fun Y : Operator D => L Y p.1 p.2)
    (fullMatrixUnit_decomposition X)
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  simpa only [fullOpMatrix, fullVec, Matrix.mulVec, dotProduct, mul_comm] using h

/-- The complete matrix of a single first-order factor acts on every input. -/
theorem fullFactorMatrix_mulVec (lam : Fin D → ℝ) (β : ℝ)
    (A X : Operator D) (a : FullCoord D) :
    (fullFactorMatrix lam β A a).mulVec (fullVec X) =
      fullVec (parentFactor (gibbsDiag lam β) (fullTransition A a) X) := by
  have h : fullFactorMatrix lam β A a =
      fullOpMatrix (parentFactor (gibbsDiag lam β) (fullTransition A a)) := by
    funext p q
    exact fullFactorMatrix_eq_parentFactor lam β A a p q
  rw [h, fullOpMatrix_mulVec]

/-- The adjoint product has exactly the conjugate-first Gram entry of the
actual factors. No frequency-injectivity hypothesis enters this identity. -/
theorem fullFactorGram_entry (lam : Fin D → ℝ) (β : ℝ) (A : Operator D)
    (a b p q : FullCoord D) :
    ((fullFactorMatrix lam β A a)ᴴ * fullFactorMatrix lam β A b) p q =
      hsInner
        (parentFactor (gibbsDiag lam β) (fullTransition A a) (matUnit p.1 p.2 1))
        (parentFactor (gibbsDiag lam β) (fullTransition A b) (matUnit q.1 q.2 1)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    fullFactorMatrix_eq_parentFactor, hsInner_eq_sum, Fintype.sum_prod_type]

/-- Full Parent Op apply for the stated finite source data. -/
theorem fullParentOp_apply (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    fullParentOp lam β kern A X =
      ∑ P, parentGramFamOp (fullWeight lam β kern) (gibbsDiag lam β)
        (fullTransition (A P)) X := by
  simp only [fullParentOp, LinearMap.sum_apply]

/-- The independently assembled matrix is the actual physical parent's
matrix, entry by entry, including the physical half and complex adjoints. -/
theorem fullGramMatrix_entry (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (p q : FullCoord D) :
    fullGramMatrix lam β kern A p q =
      (fullParentOp lam β kern A (matUnit q.1 q.2 1)) p.1 p.2 := by
  classical
  have h : hsInner (matUnit p.1 p.2 1)
      (fullParentOp lam β kern A (matUnit q.1 q.2 1)) =
      fullGramMatrix lam β kern A p q := by
    simp only [fullParentOp, LinearMap.sum_apply, parentGramFamOp_apply,
      hsInner_sum_right, hsInner_smul_right, fullGramMatrix,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun P _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hsInner_parentFactor_adjoint (fourthRoot_isHermitian _), fullFactorGram_entry]
  simpa only [fullHsInner_matUnit] using h.symm

/-- Full vectorized action of the physical source-weighted parent, for every
complex input and with every transition and proposal retained. -/
theorem fullGramMatrix_mulVec (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    (fullGramMatrix lam β kern A).mulVec (fullVec X) =
      fullVec (fullParentOp lam β kern A X) := by
  have h : fullGramMatrix lam β kern A = fullOpMatrix (fullParentOp lam β kern A) := by
    funext p q
    exact fullGramMatrix_entry lam β kern A p q
  rw [h, fullOpMatrix_mulVec]

/-- The actual parent kills the Gibbs square root. Positivity of the state
is a structural input here; no positivity or injectivity of the weight is used. -/
theorem fullParentOp_sqrt_eq_zero (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (hρ : (gibbsDiag lam β).PosDef) :
    fullParentOp lam β kern A (CFC.sqrt (gibbsDiag lam β)) = 0 := by
  classical
  rw [fullParentOp_apply]
  exact Finset.sum_eq_zero fun P _ =>
    parentGramFamOp_sqrt_eq_zero hρ (fullWeight lam β kern) (fullTransition (A P))

/-- The same Gibbs vector is killed by the independently assembled full
matrix, by transport through the proved operator-to-matrix bridge. -/
theorem fullGramMatrix_sqrt_eq_zero (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (hρ : (gibbsDiag lam β).PosDef) :
    (fullGramMatrix lam β kern A).mulVec (fullVec (CFC.sqrt (gibbsDiag lam β))) = 0 := by
  rw [fullGramMatrix_mulVec, fullParentOp_sqrt_eq_zero lam β kern A hρ]
  rfl

end Qatlib.Concepts.GibbsSource.SourceForms
