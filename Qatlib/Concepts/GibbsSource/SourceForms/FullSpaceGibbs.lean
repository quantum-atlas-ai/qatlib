/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceAssembly

@[expose] public section


/-! # The actual full-space Gibbs null vector

The diagonal Gibbs matrix used by `parentFactor` is normalized by its
partition function. The full matrix coordinates used in the analytic
calculation instead contain `exp (-beta * lambda_i / 2)` on the diagonal.
This module proves their precise positive scalar relation and transports
the existing source-factor annihilation theorem through the complete
operator-to-matrix bridge.

There is no restriction on the real temperature parameter, on repeated
Bohr frequencies, on the damping kernel, or on the proposal family. A
nonempty original Hilbert space is used to prove the partition function
positive and the resulting vector nonzero. No positivity of the assembled
parent or of its weights is assumed in the annihilation statements.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ}

/-- The actual partition function of the full, uncompressed spectrum. -/
noncomputable def fullGibbsPartition (lam : Fin D → ℝ) (β : ℝ) : ℝ :=
  ∑ i : Fin D, Real.exp (-(β * lam i))

/-- The unnormalized square-root Gibbs matrix, retaining all original levels. -/
noncomputable def fullGibbsMatrix (lam : Fin D → ℝ) (β : ℝ) : Operator D :=
  Matrix.diagonal (fun i => ((Real.exp (-(β * lam i) / 2) : ℝ) : ℂ))

/-- The full matrix-unit coordinates of the unnormalized Gibbs matrix. -/
noncomputable def fullGibbsVector (lam : Fin D → ℝ) (β : ℝ) : FullCoord D → ℂ :=
  fullVec (fullGibbsMatrix lam β)

/-- The partition sum is strictly positive on every nonempty finite space. -/
theorem fullGibbsPartition_pos [Nonempty (Fin D)] (lam : Fin D → ℝ) (β : ℝ) :
    0 < fullGibbsPartition lam β := by
  classical
  obtain ⟨i⟩ := ‹Nonempty (Fin D)›
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩

/-- The library's normalized diagonal Gibbs state is genuinely positive definite. -/
theorem fullGibbsDiag_posDef [Nonempty (Fin D)] (lam : Fin D → ℝ) (β : ℝ) :
    (gibbsDiag lam β).PosDef := by
  unfold gibbsDiag
  apply Matrix.PosDef.diagonal
  intro i
  apply Complex.zero_lt_real.mpr
  exact div_pos (Real.exp_pos _) (fullGibbsPartition_pos lam β)

/-- Exact diagonal formula for the normalized Gibbs square root. -/
theorem fullGibbs_sqrt_diagonal [Nonempty (Fin D)] (lam : Fin D → ℝ) (β : ℝ) :
    CFC.sqrt (gibbsDiag lam β) =
      Matrix.diagonal (fun i =>
        ((Real.sqrt (Real.exp (-(β * lam i)) / fullGibbsPartition lam β) : ℝ) : ℂ)) := by
  have hf : ∀ i : Fin D,
      0 ≤ Real.exp (-(β * lam i)) / fullGibbsPartition lam β :=
    fun i => (div_pos (Real.exp_pos _) (fullGibbsPartition_pos lam β)).le
  simpa only [gibbsDiag, fullGibbsPartition] using
    CFC_sqrt_diagonal
      (fun i : Fin D => Real.exp (-(β * lam i)) / fullGibbsPartition lam β) hf

/-- The analytic Gibbs matrix differs from the library's square root by exactly `sqrt Z`. -/
theorem fullGibbsMatrix_eq_smul_sqrt [Nonempty (Fin D)]
    (lam : Fin D → ℝ) (β : ℝ) :
    fullGibbsMatrix lam β =
      ((Real.sqrt (fullGibbsPartition lam β) : ℝ) : ℂ) •
        CFC.sqrt (gibbsDiag lam β) := by
  have hs : Real.sqrt (fullGibbsPartition lam β) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (fullGibbsPartition_pos lam β))
  have he (i : Fin D) :
      Real.sqrt (fullGibbsPartition lam β) *
        Real.sqrt (Real.exp (-(β * lam i)) / fullGibbsPartition lam β) =
          Real.exp (-(β * lam i) / 2) := by
    rw [Real.sqrt_div (Real.exp_nonneg _) (fullGibbsPartition lam β), sqrt_exp]
    field_simp [hs]
  rw [fullGibbs_sqrt_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [fullGibbsMatrix, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul]
    rw [← Complex.ofReal_mul, he]
  · simp [fullGibbsMatrix, Matrix.smul_apply, smul_eq_mul, hij]

/-- Each diagonal coordinate of the full vector is the prescribed Boltzmann amplitude. -/
theorem fullGibbsVector_diag (lam : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    fullGibbsVector lam β (i, i) = ((Real.exp (-(β * lam i) / 2) : ℝ) : ℂ) := by
  simp only [fullGibbsVector, fullVec, fullGibbsMatrix, Matrix.diagonal_apply_eq]

/-- The Gibbs vector is a nonzero vector, rather than only a formal kernel expression. -/
theorem fullGibbsVector_ne_zero [Nonempty (Fin D)] (lam : Fin D → ℝ) (β : ℝ) :
    fullGibbsVector lam β ≠ 0 := by
  obtain ⟨i⟩ := ‹Nonempty (Fin D)›
  intro hz
  have hi := congrFun hz (i, i)
  rw [fullGibbsVector_diag] at hi
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))) hi

/-- The associated full Gibbs matrix is nonzero as an operator. -/
theorem fullGibbsMatrix_ne_zero [Nonempty (Fin D)] (lam : Fin D → ℝ) (β : ℝ) :
    fullGibbsMatrix lam β ≠ 0 := by
  intro hz
  apply fullGibbsVector_ne_zero lam β
  rw [fullGibbsVector, hz]
  rfl

/-- Every actual first-order factor kills the unnormalized full Gibbs matrix. -/
theorem fullParentFactor_gibbsMatrix_eq_zero [Nonempty (Fin D)]
    (lam : Fin D → ℝ) (β : ℝ) (B : Operator D) :
    parentFactor (gibbsDiag lam β) B (fullGibbsMatrix lam β) = 0 := by
  rw [fullGibbsMatrix_eq_smul_sqrt, map_smul,
    parentFactor_sqrt (fullGibbsDiag_posDef lam β), smul_zero]

/-- The complete matrix of every actual transition factor kills that same vector. -/
theorem fullFactorMatrix_gibbsVector_eq_zero [Nonempty (Fin D)]
    (lam : Fin D → ℝ) (β : ℝ) (A : Operator D) (a : FullCoord D) :
    (fullFactorMatrix lam β A a).mulVec (fullGibbsVector lam β) = 0 := by
  rw [fullGibbsVector, fullFactorMatrix_mulVec, fullParentFactor_gibbsMatrix_eq_zero]
  rfl

/-- The actual source-weighted parent kills the full Gibbs matrix for every kernel. -/
theorem fullParentOp_gibbsMatrix_eq_zero [Nonempty (Fin D)]
    {ι : Type*} [Fintype ι] (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) :
    fullParentOp lam β kern A (fullGibbsMatrix lam β) = 0 := by
  rw [fullGibbsMatrix_eq_smul_sqrt, map_smul,
    fullParentOp_sqrt_eq_zero lam β kern A (fullGibbsDiag_posDef lam β), smul_zero]

/-- Full-space annihilation by the independently assembled physical Gram matrix.
Repeated frequencies and arbitrary real kernels are allowed. -/
theorem fullGramMatrix_gibbsVector_eq_zero [Nonempty (Fin D)]
    {ι : Type*} [Fintype ι] (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) :
    (fullGramMatrix lam β kern A).mulVec (fullGibbsVector lam β) = 0 := by
  rw [fullGibbsVector, fullGramMatrix_mulVec, fullParentOp_gibbsMatrix_eq_zero]
  rfl

end Qatlib.Concepts.GibbsSource.SourceForms
