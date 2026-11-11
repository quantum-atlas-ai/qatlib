/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Pair-swap symmetry projectors

This module gives the actual two-particle swap action and its symmetric and antisymmetric sector
operators for the symmetry-readout setting of [Whitfield2013]. The character-weighted sum
`wigner` equals the explicit formula `sector`, and both sector operators are Hermitian and
idempotent.

## Main statements

* `action_mul`: Boolean exclusive-or corresponds to multiplication of the identity-and-swap
  action.
* `wigner_eq_sector`: the Wigner sum equals half the identity plus the signed swap.
* `sectors_sum` and `projected_symmetry`: completeness and the selected swap eigenvalue
  equation.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Papers.SpinFreeSim13.PairProjector
open Matrix
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The permutation interchanging the two components of a pair. -/
def swapPerm (I : Type*) : Equiv.Perm (I × I) := Equiv.prodComm I I

/-- The complex permutation matrix interchanging two particle indices. -/
def swapMatrix : Matrix (I × I) (I × I) ℂ := (swapPerm I).permMatrix ℂ

/-- The pair-swap matrix squares to the identity. -/
theorem swap_square : (swapMatrix (I:=I)) * swapMatrix = 1 := by
  rw [swapMatrix, ← Matrix.permMatrix_mul]
  have h : swapPerm I * swapPerm I = 1 := by apply Equiv.ext; rintro ⟨i,j⟩; rfl
  rw [h]
  simp

omit [Fintype I] in

/-- The pair-swap matrix equals its conjugate transpose. See [Whitfield2013]. -/
theorem swap_hermitian : (swapMatrix (I:=I))ᴴ = swapMatrix := by
  rw [swapMatrix, Matrix.conjTranspose_permMatrix]
  congr 1

/-- The pair-swap matrix acts on amplitudes by interchanging their two arguments. See
[Whitfield2013]. -/
theorem swap_apply (ψ : I × I → ℂ) (i j : I) :
    (swapMatrix *ᵥ ψ) (i,j) = ψ (j,i) := by
  rw [swapMatrix, Matrix.permMatrix_mulVec]
  rfl

/-- The Boolean-indexed pair action, assigning the identity to `false` and the swap matrix to
`true`. -/
def action (g : Bool) : Matrix (I × I) (I × I) ℂ := if g then swapMatrix else 1

/-- The pair action converts Boolean exclusive-or into matrix multiplication. See
[Whitfield2013]. -/
theorem action_mul (g h : Bool) : action (I:=I) (g ^^ h) = action g * action h := by
  cases g <;> cases h <;> simp [action, swap_square]

/-- The trivial or sign character of the Boolean pair-swap group, selected by `label`. -/
def character (label g : Bool) : ℂ := if label && g then -1 else 1

/-- The complex scalar one for the symmetric label and minus one for the antisymmetric label. -/
def sign (label : Bool) : ℂ := if label then -1 else 1

/-- The scalar selected by a symmetry label squares to one. -/
theorem sign_square (label : Bool) : sign label * sign label = 1 := by
  cases label <;> norm_num [sign]

/-- The character-weighted two-element Wigner sum for the identity-and-swap action. -/
def wigner (label : Bool) : Matrix (I × I) (I × I) ℂ :=
  (2⁻¹ : ℂ) • ∑ g : Bool, star (character label g) • action g

/-- The pair-symmetry operator `(1 / 2) • (1 + sign label • swapMatrix)`. -/
def sector (label : Bool) : Matrix (I × I) (I × I) ℂ :=
  (2⁻¹ : ℂ) • (1 + sign label • swapMatrix)

omit [Fintype I] in

/-- The two-element character-weighted Wigner sum equals the explicit symmetric or antisymmetric
sector operator. See [Whitfield2013]. -/
theorem wigner_eq_sector (label : Bool) : wigner (I:=I) label = sector label := by
  cases label <;> simp [wigner, character, action, sector, sign] <;> abel

/-- Each pair-symmetry sector operator is idempotent. See [Whitfield2013]. -/
theorem sector_square (label : Bool) : sector (I:=I) label * sector label = sector label := by
  have h : (1 + sign label • (swapMatrix (I:=I))) * (1 + sign label • swapMatrix) =
      (2 : ℂ) • (1 + sign label • swapMatrix) := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, swap_square, sign_square, one_smul]
    module
  rw [sector, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
  norm_num

omit [Fintype I] in

/-- Each pair-symmetry sector operator is Hermitian. See [Whitfield2013]. -/
theorem sector_hermitian (label : Bool) : (sector (I:=I) label)ᴴ = sector label := by
  cases label <;> simp [sector, sign, swap_hermitian]

omit [Fintype I] in

/-- The symmetric and antisymmetric sector operators sum to the identity. -/
theorem sectors_sum : sector (I:=I) false + sector true = 1 := by
  simp only [sector, sign, Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul]
  module

/-- Left multiplication by swap scales a sector operator by its selected sign. -/
theorem swap_sector (label : Bool) :
    swapMatrix (I:=I) * sector label = sign label • sector label := by
  rw [sector, Matrix.mul_smul, mul_add, mul_one, Matrix.mul_smul, swap_square]
  cases label <;> simp only [sign, Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul]
  all_goals module

/-- The amplitude obtained by applying a sector operator is a swap eigenvector with the selected
sign, including the possible zero vector. See [Whitfield2013]. -/
theorem projected_symmetry (label : Bool) (ψ : I × I → ℂ) :
    swapMatrix *ᵥ (sector label *ᵥ ψ) = sign label • (sector label *ᵥ ψ) := by
  rw [Matrix.mulVec_mulVec, swap_sector, Matrix.smul_mulVec]

/-- A sector-projected amplitude at `(i, j)` is half the original amplitude plus its
sign-weighted transposed amplitude. -/
theorem sector_apply (label : Bool) (ψ : I × I → ℂ) (i j : I) :
    (sector label *ᵥ ψ) (i,j) = (2⁻¹ : ℂ) * (ψ (i,j) + sign label * ψ (j,i)) := by
  rw [sector, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  change (2⁻¹ : ℂ) * (ψ (i,j) + sign label * ((swapMatrix *ᵥ ψ) (i,j))) = _
  rw [swap_apply]
end Qatlib.Papers.SpinFreeSim13.PairProjector
