/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Swap-test readout of register overlap

This module constructs the Hadamard-controlled-swap-Hadamard matrix `circuit` and proves its
unitarity and output amplitudes. The difference between its two control outcome weights equals
the squared modulus of the input registers' Hermitian inner product, without requiring
normalized input vectors.

The scaled identities account for a common input amplitude, and `flagLift` extends an operator
while preserving an additional flag register.

The mathematical background is discussed in [NielsenChuang2010].

## Main statements

* `circuit_output`: computes the symmetric and antisymmetric output amplitudes.
* `actual_born_overlap`: identifies the control weight difference with squared overlap.
* `actual_scaled_born_overlap`: gives the corresponding scaled identity.
* `flagLift_unitary`: preserves unitarity when adding an untouched flag register.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace Qatlib.Foundations.TensorRegisters.SwapReadout

/-- The complex scalar `1 / sqrt 2` used to normalize the Hadamard matrix. -/
def r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The Hadamard normalization scalar is fixed by complex conjugation. -/
theorem star_r : star r = r := by simp [r]

/-- The square of the Hadamard normalization scalar is one half. -/
theorem r_mul_r : r * r = (1/2 : ℂ) := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℝ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  unfold r
  rw [← mul_inv, h]
  norm_num

/-- The Boolean-indexed Hadamard matrix with entry `-r` only when both indices are true and
entry `r` otherwise. -/
def had : Matrix Bool Bool ℂ := fun a b => if a && b then -r else r

/-- The Boolean-indexed Hadamard matrix is unitary. -/
theorem had_unitary : had ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change hadᴴ * had = 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool]
  have hr : (starRingEnd ℂ) r = r := star_r
  cases a <;> cases b <;> norm_num [had, hr, r_mul_r]

/-- Apply the Hadamard matrix to the Boolean control while leaving the two data registers
unchanged. -/
def hadFirst {I : Type*} [DecidableEq I] :
    Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ :=
  had ⊗ₖ (1 : Matrix (I × I) (I × I) ℂ)

/-- The permutation that exchanges the two data registers exactly when the Boolean control is
true. -/
def swapPerm (I : Type*) : Equiv.Perm (Bool × (I × I)) where
  toFun z := if z.1 then (true, (z.2.2,z.2.1)) else (false,z.2)
  invFun z := if z.1 then (true, (z.2.2,z.2.1)) else (false,z.2)
  left_inv z := by rcases z with ⟨b,i,j⟩; cases b <;> rfl
  right_inv z := by rcases z with ⟨b,i,j⟩; cases b <;> rfl

/-- The permutation matrix implementing the controlled exchange of the two data registers. -/
def controlledSwap {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ :=
  Equiv.Perm.permMatrix ℂ (swapPerm I)

/-- The swap-test matrix obtained by a Hadamard on the control, a controlled swap, and a second
Hadamard on the control. -/
def circuit {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ := hadFirst * controlledSwap * hadFirst

/-- The Hadamard acting on the control register is unitary on the full register. -/
theorem hadFirst_unitary {I : Type*} [Fintype I] [DecidableEq I] :
    hadFirst (I:=I) ∈ Matrix.unitaryGroup (Bool × (I × I)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (had ⊗ₖ (1 : Matrix (I × I) (I × I) ℂ))ᴴ * (had ⊗ₖ 1) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hh := Matrix.mem_unitaryGroup_iff'.mp had_unitary
  change hadᴴ * had = 1 at hh
  rw [hh]
  simp

/-- The controlled-swap matrix is unitary. -/
theorem controlledSwap_unitary {I : Type*} [Fintype I] [DecidableEq I] :
    controlledSwap (I:=I) ∈ Matrix.unitaryGroup (Bool × (I × I)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (Equiv.Perm.permMatrix ℂ (swapPerm I))ᴴ * Equiv.Perm.permMatrix ℂ (swapPerm I) = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The swap-test circuit matrix is unitary. -/
theorem circuit_unitary {I : Type*} [Fintype I] [DecidableEq I] :
    circuit (I:=I) ∈ Matrix.unitaryGroup (Bool × (I × I)) ℂ :=
  (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem hadFirst_unitary controlledSwap_unitary) hadFirst_unitary

/-- Evaluate the Hadamard action on the control as the normalized sum or difference of the two
control amplitudes. -/
theorem hadFirst_apply {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : Bool × (I × I) → ℂ) (b : Bool) (i j : I) :
    (hadFirst *ᵥ ψ) (b,(i,j)) =
      r * (ψ (false,(i,j)) + if b then -ψ (true,(i,j)) else ψ (true,(i,j))) := by
  simp only [hadFirst, mulVec, dotProduct, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Fintype.sum_bool]
  cases b <;> simp [had, ite_and] <;> ring

/-- A controlled swap exchanges the two data indices on the true control branch and preserves
them on the false branch. -/
theorem controlledSwap_apply {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : Bool × (I × I) → ℂ) (b : Bool) (i j : I) :
    (controlledSwap *ᵥ ψ) (b,(i,j)) =
      if b then ψ (true,(j,i)) else ψ (false,(i,j)) := by
  rw [controlledSwap, Matrix.permMatrix_mulVec]
  cases b <;> rfl

/-- The tensor amplitude `u i * v j` on the false control branch, with zero amplitude on the
true branch. -/
def input {I : Type*} (u v : I → ℂ) (z : Bool × (I × I)) : ℂ :=
  if z.1 then 0 else u z.2.1 * v z.2.2

/-- The swap-test output amplitude is half the symmetric tensor sum for false control and half
the antisymmetric tensor difference for true control. -/
theorem circuit_output {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → ℂ) (b : Bool) (i j : I) :
    (circuit *ᵥ input u v) (b,(i,j)) =
      (1/2 : ℂ) * (u i * v j + if b then -(u j * v i) else u j * v i) := by
  rw [circuit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hadFirst_apply]
  rw [controlledSwap_apply, controlledSwap_apply]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hadFirst_apply, hadFirst_apply]
  cases b <;> simp [input]
  · linear_combination r_mul_r * (u i * v j + u j * v i)
  · linear_combination r_mul_r * (u i * v j - u j * v i)

/-- The sum of squared output amplitudes over the data registers at the specified Boolean
control outcome. -/
def outcomeWeight {I : Type*} [Fintype I] [DecidableEq I] (u v : I → ℂ) (b : Bool) : ℝ :=
  ∑ i, ∑ j, Complex.normSq ((circuit *ᵥ input u v) (b,(i,j)))

/-- Each control outcome weight is nonnegative. -/
theorem outcomeWeight_nonneg {I : Type*} [Fintype I] [DecidableEq I] (u v : I → ℂ) (b : Bool) :
    0 ≤ outcomeWeight u v b := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- The difference of the squared moduli of the half-sum and half-difference equals half the sum
of the two conjugate cross terms. -/
theorem norm_difference (a b : ℂ) :
    (Complex.normSq ((1/2:ℂ)*(a+b)) : ℂ) - (Complex.normSq ((1/2:ℂ)*(a+ -b)) : ℂ) =
      (star a*b+star b*a)/2 := by
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def, map_mul, map_div₀, map_add, map_neg, map_ofNat, map_one]
  ring

/-- The sum of tensor cross terms under exchange of the two registers equals the squared modulus
of their Hermitian inner product. -/
theorem swap_sum_overlap {I : Type*} [Fintype I] (u v : I → ℂ) :
    (∑ i, ∑ j, star (u i*v j)*(u j*v i)) = (Complex.normSq (star u ⬝ᵥ v):ℂ) := by
  simp only [star_mul, Complex.normSq_eq_conj_mul_self, dotProduct, map_sum,
    map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The false control outcome weight minus the true control outcome weight equals the squared
modulus of the input inner product. -/
theorem actual_born_overlap {I : Type*} [Fintype I] [DecidableEq I] (u v : I → ℂ) :
    outcomeWeight u v false - outcomeWeight u v true = Complex.normSq (star u ⬝ᵥ v) := by
  apply Complex.ofReal_injective
  simp only [outcomeWeight, Complex.ofReal_sub, Complex.ofReal_sum, circuit_output,
    Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, norm_difference]
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, star (u j*v i)*(u i*v j)) = ∑ i, ∑ j, star (u i*v j)*(u j*v i) := by
    rw [Finset.sum_comm]
  rw [hswap, swap_sum_overlap]
  ring

/-- The control outcome weight after multiplying the swap-test input by a common complex scalar
`a`. -/
def scaledWeight {I : Type*} [Fintype I] [DecidableEq I] (a : ℂ) (u v : I → ℂ) (b : Bool) : ℝ :=
  ∑ i, ∑ j, Complex.normSq ((circuit *ᵥ (a • input u v)) (b,(i,j)))

/-- Scaling the input by `a` multiplies each outcome weight by `Complex.normSq a`. -/
theorem scaledWeight_eq {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (u v : I → ℂ) (b : Bool) :
    scaledWeight a u v b = Complex.normSq a * outcomeWeight u v b := by
  simp only [scaledWeight, outcomeWeight, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul, map_mul, Finset.mul_sum]

/-- For input scaled by `a`, the control weight difference is `Complex.normSq a` times the
squared modulus of the input inner product. -/
theorem actual_scaled_born_overlap {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (u v : I → ℂ) :
    scaledWeight a u v false - scaledWeight a u v true =
      Complex.normSq a * Complex.normSq (star u ⬝ᵥ v) := by
  rw [scaledWeight_eq, scaledWeight_eq, ← mul_sub, actual_born_overlap]

/-- Extend an operator by the identity on an additional flag register using a Kronecker product. -/
def flagLift {F J : Type*} [DecidableEq F] (A : Matrix J J ℂ) : Matrix (F×J) (F×J) ℂ :=
  (1 : Matrix F F ℂ) ⊗ₖ A

/-- The lifted operator acts independently on the amplitude slice at each fixed flag value. -/
theorem flagLift_apply {F J : Type*} [Fintype F] [Fintype J] [DecidableEq F]
    (A : Matrix J J ℂ) (ψ : F×J→ℂ) (f : F) (j : J) :
    (flagLift A *ᵥ ψ) (f,j) = (A *ᵥ (fun x => ψ (f,x))) j := by
  simp [flagLift, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul]

/-- Extending a unitary operator by the identity on a finite flag register preserves unitarity. -/
theorem flagLift_unitary {F J : Type*} [Fintype F] [Fintype J] [DecidableEq F] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A∈Matrix.unitaryGroup J ℂ) :
    flagLift (F:=F) A ∈ Matrix.unitaryGroup (F×J) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change ((1 : Matrix F F ℂ) ⊗ₖ A)ᴴ * (1 ⊗ₖ A) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  change Aᴴ*A=1 at h
  rw [h]
  simp

/-- The squared modulus of the Hermitian inner product is unchanged when the two inputs are
exchanged. -/
theorem overlap_symm {I : Type*} [Fintype I] (u v : I → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) = Complex.normSq (star v ⬝ᵥ u) := by
  have h : star (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
    simp only [dotProduct, star_sum, star_mul, Pi.star_apply, star_star]
  rw [← h]
  exact (Complex.normSq_conj _).symm

end Qatlib.Foundations.TensorRegisters.SwapReadout
