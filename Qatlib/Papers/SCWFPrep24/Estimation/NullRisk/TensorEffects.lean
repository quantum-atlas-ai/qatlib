/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.GramEffects
import QuantumInfo.ForMathlib.HermitianMat.Inner
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor Effects

The canonical positive rank-one effect associated to an arbitrary complete-register vector.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
open Matrix
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The canonical positive rank-one effect associated to an arbitrary complete-register vector. -/
def vectorEffect {I : Type*} [Fintype I] (ψ : I → ℂ) : HermitianMat I ℂ :=
  ⟨Matrix.vecMulVec ψ (star ψ), (Matrix.posSemidef_vecMulVec_self_star ψ).isHermitian⟩

/-- The literal quadratic Born weight is the canonical Hermitian trace pairing with the actual pure-state matrix. -/
theorem effectWeight_eq_vector_inner {I : Type*} [Fintype I]
    (E : HermitianMat I ℂ) (ψ : I → ℂ) :
    effectWeight E ψ = inner ℝ (vectorEffect ψ) E := by
  rw [HermitianMat.inner_eq_re_trace]
  change (∑ i, star (ψ i)*(∑ j, E.mat i j*ψ j)).re =
    (Matrix.trace (Matrix.vecMulVec ψ (star ψ)*E.mat)).re
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two-copy vector is the tensor product of the SAME supplied input with itself. -/
def pairedState {I : Type*} (ψ : I → ℂ) (z : I × I) : ℂ := ψ z.1*ψ z.2

/-- Its literal pure-state matrix is the tensor product of the same pure-state matrix. -/
theorem pairedState_vectorEffect {I : Type*} [Fintype I] (ψ : I → ℂ) :
    vectorEffect (pairedState ψ) = vectorEffect ψ ⊗ₖ vectorEffect ψ := by
  apply HermitianMat.ext
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [vectorEffect, pairedState, HermitianMat.mat_mk, HermitianMat.kronecker_mat,
    Matrix.vecMulVec_apply, Matrix.kronecker_apply, Pi.star_apply, star_mul]
  ring

/-- The canonical Hermitian real inner product casts to its exact complex matrix trace. -/
theorem complex_inner_trace {J : Type*} [Fintype J] (A B : HermitianMat J ℂ) :
      (inner ℝ A B : ℂ) = Matrix.trace (A.mat*B.mat) :=
  HermitianMat.inner_eq_trace_mul A B

/-- The actual two-copy tensor-product effect has exactly the product of the two actual one-copy Born weights. -/
theorem effectWeight_kronecker_same_input {I : Type*} [Fintype I]
    (E F : HermitianMat I ℂ) (ψ : I → ℂ) :
    effectWeight (E ⊗ₖ F) (pairedState ψ) = effectWeight E ψ*effectWeight F ψ := by
  simp_rw [effectWeight_eq_vector_inner]
  rw [pairedState_vectorEffect]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, complex_inner_trace, complex_inner_trace, complex_inner_trace]
  simp only [HermitianMat.kronecker_mat]
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- The real Born weight is linear in a finite sum of actual Hermitian effects. -/
theorem effectWeight_sum {I K : Type*} [Fintype I] [Fintype K]
    (E : K → HermitianMat I ℂ) (ψ : I → ℂ) :
    effectWeight (∑ k, E k) ψ = ∑ k, effectWeight (E k) ψ := by
  unfold effectWeight
  simp only [HermitianMat.mat_finset_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- Every actual finite separable effect has its literal finite product-probability expansion on two identical supplied copies. -/
theorem effectWeight_finite_separable_same_input {I K : Type*} [Fintype I] [Fintype K]
    (E F : K → HermitianMat I ℂ) (ψ : I → ℂ) :
    effectWeight (∑ k, E k ⊗ₖ F k) (pairedState ψ) =
      ∑ k, effectWeight (E k) ψ*effectWeight (F k) ψ := by
  rw [effectWeight_sum]
  simp only [effectWeight_kronecker_same_input]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
