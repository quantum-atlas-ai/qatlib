/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.Lemma6Matrix
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Unitarity of the controlled matrix construction

This module identifies `uBMat` with a tensor product containing identity factors and proves that
the controlled-operation construction preserves unitarity. It also shows that taking the
conjugate transpose commutes with both `uBMat` and `lemma6Mat`. The development follows
[Kitaev1995].

## Main statements

* `uBMat_eq_tensorGate`: expresses the lifted matrix as a tensor product.
* `lemma6Mat_unitary`: proves unitarity of the five-block construction for unitary input.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- The lifted matrix `uBMat U` equals the tensor product of the control identity, the
first-register identity, and `U`, as used in [Kitaev1995]. -/
theorem uBMat_eq_tensorGate (U : Matrix (Reg n) (Reg n) ℂ) :
    uBMat U = TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) U) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨p21, p22⟩ := p2
  obtain ⟨q21, q22⟩ := q2
  simp only [uBMat, Matrix.of_apply, TensorGate, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p21 = q21 <;> simp [h1, h2]

/-- Lifting a unitary `U` to the second data register gives a unitary matrix on the full
controlled memory, as used in [Kitaev1995]. -/
theorem uBMat_unitary (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    uBMat U ∈ Matrix.unitaryGroup (CtrlMem n) ℂ := by
  rw [uBMat_eq_tensorGate]
  exact tensorGate_unitary (Matrix.unitaryGroup _ ℂ).one_mem
    (tensorGate_unitary (Matrix.unitaryGroup _ ℂ).one_mem hU)

/-- The conjugate transpose of `uBMat U` is `uBMat` applied to the conjugate transpose of `U`. -/
theorem uBMat_conjTranspose (U : Matrix (Reg n) (Reg n) ℂ) :
    (uBMat U)ᴴ = uBMat (Uᴴ) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨p21, p22⟩ := p2
  obtain ⟨q21, q22⟩ := q2
  simp only [uBMat, Matrix.of_apply, Matrix.conjTranspose_apply]
  by_cases h1 : p1 = q1
  · subst h1
    by_cases h2 : p21 = q21
    · subst h2; simp
    · have h2' : ¬ q21 = p21 := fun e => h2 e.symm
      simp [h2, h2']
  · have h1' : ¬ q1 = p1 := fun e => h1 e.symm
    simp [h1, h1']

/-- The conjugate transpose of the five-block construction equals the same construction with
`Uᴴ`, as used in [Kitaev, 1995, Lemma 6][Kitaev1995]. -/
theorem lemma6Mat_conjTranspose (U : Matrix (Reg n) (Reg n) ℂ) :
    (lemma6Mat U)ᴴ = lemma6Mat (Uᴴ) := by
  unfold lemma6Mat
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  rw [permMatrix_conjTranspose ccopyAB_involutive,
    permMatrix_conjTranspose ccopyBA_involutive, uBMat_conjTranspose]
  simp only [mul_assoc]

/-- The matrix `lemma6Mat U` is unitary whenever `U` is unitary, validating the matrix
construction for [Kitaev, 1995, Lemma 6][Kitaev1995]. -/
theorem lemma6Mat_unitary (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    lemma6Mat U ∈ Matrix.unitaryGroup (CtrlMem n) ℂ := by
  unfold lemma6Mat
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem
      ((Matrix.unitaryGroup _ ℂ).mul_mem
        ((Matrix.unitaryGroup _ ℂ).mul_mem
          (permMatrix_unitary ccopyAB_involutive)
          (permMatrix_unitary ccopyBA_involutive))
        (uBMat_unitary U hU))
      (permMatrix_unitary ccopyBA_involutive))
    (permMatrix_unitary ccopyAB_involutive)

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
