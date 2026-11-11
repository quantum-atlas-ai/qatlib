/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result

/-!
# A two qubit Bell circuit for HOM overlap readout

`homBell` composes the real CNOT matrix with a Hadamard on the first qubit. The module gives its
entries and verifies orthogonality.

The sign observable `homPairSign` is negative only on the outcome with both bits true.
`homBell_parity_swap` shows that conjugating this observable by the Bell circuit yields the swap
matrix, providing the local identity for overlap readout. See [BaskaranEtAl2023].

## Main statements

* `homBell_orthogonal`: The columns of the real Bell circuit matrix are orthonormal.
* `homBell_parity_swap`: The Bell circuit's sign weighted column pairing equals the matrix entry
  of the two qubit swap.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.HHLManyBody22.HomOverlap
open Matrix

/-- The real single qubit Hadamard entry, with sign `-1` only when both indices are true and
scale `1 / sqrt 2`. -/
def homHadamard (a b : Bool) : ℝ := (if a && b then -1 else 1)/Real.sqrt 2

/-- The real CNOT matrix sending `(a,b)` to `(a, xor a b)`. -/
def homCnot : Matrix (Bool×Bool) (Bool×Bool) ℝ :=
  fun z x => if z=(x.1,Bool.xor x.1 x.2) then 1 else 0

/-- The real two qubit matrix applying a Hadamard to the first bit and leaving the second bit
unchanged. -/
def homHadamardFirst : Matrix (Bool×Bool) (Bool×Bool) ℝ :=
  fun z x => if z.2=x.2 then homHadamard z.1 x.1 else 0

/-- The real Bell circuit matrix obtained by applying CNOT and then Hadamard to the first bit. -/
def homBell : Matrix (Bool×Bool) (Bool×Bool) ℝ := homHadamardFirst*homCnot

/-- A Bell circuit entry is the first bit Hadamard entry when the output second bit is the XOR
of the input bits, and zero otherwise. -/
theorem homBell_entry (z x : Bool×Bool) :
    homBell z x=if z.2=Bool.xor x.1 x.2 then homHadamard z.1 x.1 else 0 := by
  rcases z with ⟨a,b⟩
  rcases x with ⟨s,t⟩
  cases a <;> cases b <;> cases s <;> cases t <;>
    simp [homBell,homHadamardFirst,homCnot,homHadamard,Matrix.mul_apply]

/-- The square of the reciprocal of `sqrt 2` is `1/2`. -/
theorem hom_inv_sqrt_two_sq : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹=(1/2:ℝ) := by
  rw [← pow_two,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

/-- The columns of the real Bell circuit matrix are orthonormal. -/
theorem homBell_orthogonal (x y : Bool×Bool) :
    (∑z,homBell z x*homBell z y)=if x=y then 1 else 0 := by
  rcases x with ⟨s,t⟩
  rcases y with ⟨u,v⟩
  cases s <;> cases t <;> cases u <;> cases v <;>
    norm_num [homBell_entry,homHadamard,Fintype.sum_prod_type,Fintype.sum_bool,div_eq_mul_inv,
      hom_inv_sqrt_two_sq]

/-- The sign `-1` for the outcome `(true,true)` and `1` for every other bit pair. -/
def homPairSign (z : Bool×Bool) : ℝ := if z.1 && z.2 then -1 else 1

/-- The Bell circuit's sign weighted column pairing equals the matrix entry of the two qubit
swap. -/
theorem homBell_parity_swap (x y : Bool×Bool) :
    (∑z,homBell z x*homPairSign z*homBell z y)=if x=(y.2,y.1) then 1 else 0 := by
  rcases x with ⟨s,t⟩
  rcases y with ⟨u,v⟩
  cases s <;> cases t <;> cases u <;> cases v <;>
    norm_num [homBell_entry,homHadamard,homPairSign,Fintype.sum_prod_type,Fintype.sum_bool,div_eq_mul_inv,
      hom_inv_sqrt_two_sq]

end Qatlib.Papers.HHLManyBody22.HomOverlap
