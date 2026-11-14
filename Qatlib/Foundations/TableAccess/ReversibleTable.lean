/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Involutive permutation matrices for reversible tables

This module represents a finite table map by `permMatrix` and describes its action on amplitude
functions and basis kets. For an involutive map, the matrix is self-adjoint, squares to the
identity, and is unitary.

The mathematical background is discussed in [NielsenChuang2010].

## Main statements

* `permMatrix_unitary`: an involutive table map gives a unitary matrix.
* `applyGate_permMatrix`: the matrix acts by precomposition with the involution.
* `applyGate_permMatrix_ket`: a basis ket is sent to the ket of its image.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.TableAccess.ReversibleTable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The computational basis amplitude function equal to one at `j` and zero elsewhere. -/
def Ket (j : I) : I→ℂ := fun i=>if i=j then 1 else 0

/-- The matrix with entry one when the row index is `σ` applied to the column index and zero
otherwise. -/
def permMatrix (σ : I → I) : Matrix I I ℂ := Matrix.of fun i j => if i = σ j then (1 : ℂ) else 0

/-- The matrix associated with an involution squares to the identity. -/
theorem permMatrix_mul_self {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ * permMatrix σ = 1 := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ j) (fun k _ hk => by rw [ite_eq_right hk, mul_zero])
    (fun h => absurd (Finset.mem_univ (σ j)) h)]
  simp [hσ j]

omit [Fintype I] in

/-- The matrix associated with an involution equals its conjugate transpose. -/
theorem permMatrix_conjTranspose {σ : I → I} (hσ : Function.Involutive σ) :
    (permMatrix σ)ᴴ = permMatrix σ := by
  ext i j
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  by_cases hji : j = σ i
  · have hij : i = σ j := by rw [← hσ i, ← hji]
    rw [ite_eq_left hji, ite_eq_left hij, map_one]
  · have hij : i ≠ σ j := fun e => hji (by rw [← hσ j, ← e])
    rw [ite_eq_right hji, ite_eq_right hij, map_zero]

/-- The matrix associated with an involution is unitary. -/
theorem permMatrix_unitary {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, permMatrix_conjTranspose hσ]
  exact permMatrix_mul_self hσ

/-- The matrix of an involution acts on amplitudes by precomposition with that involution. -/
theorem applyGate_permMatrix {σ : I → I} (hσ : Function.Involutive σ) (ψ : I→ℂ) (i : I) :
    (permMatrix σ *ᵥ ψ) i = ψ (σ i) := by
  simp only [permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · rw [hσ i]
    simp
  · intro j _ hj
    have hne : i ≠ σ j := fun h => hj (by rw [← hσ j, ← h])
    simp [hne]
  · simp

/-- The matrix of an involution sends the ket of `j` to the ket of `σ j`. -/
theorem applyGate_permMatrix_ket {σ : I → I} (hσ : Function.Involutive σ) (j : I) :
    (permMatrix σ) *ᵥ (Ket j) = Ket (σ j) := by
  funext i
  rw [applyGate_permMatrix hσ]
  by_cases h : i = σ j
  · subst h
    simp [Ket, hσ j]
  · have h' : σ i ≠ j := fun e => h (by rw [← e, hσ i])
    simp [Ket, h, h']

end Qatlib.Foundations.TableAccess.ReversibleTable
