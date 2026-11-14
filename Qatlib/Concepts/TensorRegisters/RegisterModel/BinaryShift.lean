/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.BitVec
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Binary registers and conditional cyclic shifts

The equivalence `bitEncoding` identifies width-`n` bit vectors with residues modulo `2 ^ n`. The
matrices `stream` implement spin-controlled translations on a finite additive position group,
and `stream_mode` reduces their action on character modes to the diagonal matrix `bloch`. For
background, see [FillionGourdeauMacLeanLaflamme2017].

## Main statements

* `permU_unitary`: permutation matrices are unitary.
* `stream_mode`: character modes reduce conditional transport to spin phases.
* `spinLift_mode`: a lifted spin matrix acts on the mode's spin amplitudes.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryShift

/-- The ring equivalence between width-`n` bit vectors and `ZMod (2 ^ n)`, providing a binary
cyclic position register [FillionGourdeauMacLeanLaflamme2017]. -/
def bitEncoding (n : ℕ) : BitVec n ≃+* ZMod (2 ^ n) :=
  BitVec.equivFin.trans (ZMod.finEquiv (2 ^ n))

/-- The permutation matrix whose action sends a vector `v` to `v ∘ e.symm`. -/
def permU {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) : Matrix I I ℂ :=
  Equiv.Perm.permMatrix ℂ e.symm

/-- The matrix implementing a finite basis permutation is unitary. -/
theorem permU_unitary {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) :
    permU e ∈ Matrix.unitaryGroup I ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (Equiv.Perm.permMatrix ℂ e.symm)ᴴ * Equiv.Perm.permMatrix ℂ e.symm = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- Multiplication by `permU e` precomposes the vector with `e.symm`. -/
theorem permU_mulVec {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (v : I → ℂ) :
    permU e *ᵥ v = v ∘ e.symm := Matrix.permMatrix_mulVec (e.symm : Equiv.Perm I)

/-- The permutation adding `l` to the position when `side` is true and subtracting `l`
otherwise, while preserving spin. -/
def shift {S G : Type*} [AddCommGroup G] (side : S → Bool) (l : G) : Equiv.Perm (S × G) where
  toFun x := (x.1, if side x.1 then x.2 + l else x.2 - l)
  invFun x := (x.1, if side x.1 then x.2 - l else x.2 + l)
  left_inv x := by cases x with | mk s g => cases h : side s <;> simp [h]
  right_inv x := by cases x with | mk s g => cases h : side s <;> simp [h]

/-- The permutation matrix implementing the conditional translation `shift side l`. -/
def stream {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) : Matrix (S × G) (S × G) ℂ := permU (shift side l)

/-- The conditional translation matrix `stream side l` is unitary. -/
theorem stream_unitary {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) :
    stream side l ∈ Matrix.unitaryGroup (S × G) ℂ := permU_unitary _

/-- Conditional transport evaluates the input at `g - l` when `side s` is true and at `g + l`
otherwise [FillionGourdeauMacLeanLaflamme2017]. -/
theorem stream_apply {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) (v : S × G → ℂ) (s : S) (g : G) :
    (stream side l *ᵥ v) (s,g) = v (s, if side s then g - l else g + l) := by
  rw [stream, permU_mulVec]
  rfl

/-- The character mode `(s, g) ↦ v s * χ g` with spin amplitudes `v`. -/
def mode {S G : Type*} [AddMonoid G] (χ : AddChar G ℂ) (v : S → ℂ) : S × G → ℂ :=
  fun x => v x.1 * χ x.2

/-- The diagonal spin matrix with phase `χ (-l)` on true-side components and `χ l` on false-side
components. -/
def bloch {S G : Type*} [DecidableEq S] [AddCommGroup G] (side : S → Bool)
    (χ : AddChar G ℂ) (l : G) : Matrix S S ℂ :=
  Matrix.diagonal (fun s => χ (if side s then -l else l))

/-- Conditional transport preserves a character mode and acts on its spin amplitudes through
`bloch side χ l`. -/
theorem stream_mode {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (χ : AddChar G ℂ) (l : G) (v : S → ℂ) :
    stream side l *ᵥ mode χ v = mode χ (bloch side χ l *ᵥ v) := by
  funext x
  obtain ⟨s,g⟩ := x
  rw [stream_apply]
  cases h : side s <;>
    simp [mode, bloch, Matrix.mulVec_diagonal, h, sub_eq_add_neg, AddChar.map_add_eq_mul] <;> ring

/-- The matrix `P ⊗ₖ 1` acting on spin and leaving the position register unchanged. -/
def spinLift {S G : Type*} [DecidableEq G] (P : Matrix S S ℂ) : Matrix (S × G) (S × G) ℂ :=
  P ⊗ₖ (1 : Matrix G G ℂ)

/-- Lifting a unitary spin matrix by the identity on position gives a unitary joint-register
matrix. -/
theorem spinLift_unitary {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    (P : Matrix S S ℂ) (hP : P ∈ Matrix.unitaryGroup S ℂ) :
    spinLift (G := G) P ∈ Matrix.unitaryGroup (S × G) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (P ⊗ₖ (1 : Matrix G G ℂ))ᴴ * (P ⊗ₖ (1 : Matrix G G ℂ)) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simpa using! congrArg (fun M : Matrix S S ℂ => M ⊗ₖ (1 : Matrix G G ℂ))
    (Matrix.mem_unitaryGroup_iff'.mp hP)

/-- The lifted spin matrix sends `mode χ v` to `mode χ (P *ᵥ v)`. -/
theorem spinLift_mode {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddMonoid G] (P : Matrix S S ℂ) (χ : AddChar G ℂ) (v : S → ℂ) :
    spinLift P *ᵥ mode χ v = mode χ (P *ᵥ v) := by
  ext x
  rcases x with ⟨s,g⟩
  simp only [spinLift, mode, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- For a fixed additive character, forming a character mode is injective in its spin
amplitudes. -/
theorem mode_injective {S G : Type*} [AddMonoid G] (χ : AddChar G ℂ) :
    Function.Injective (mode (S := S) χ) := by
  intro v w he
  funext s
  have h := congrFun he (s,0)
  simpa only [mode, AddChar.map_zero_eq_one, mul_one] using h
