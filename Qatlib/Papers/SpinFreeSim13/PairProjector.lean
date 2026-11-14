/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

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
