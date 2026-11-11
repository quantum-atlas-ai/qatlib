/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Counterexamples for the printed linear-code preparation

The binary generator `generator = ![1,1]` is nonzero and spans an injectively encoded
one-dimensional code, yet it is orthogonal to every codeword in that code. The associated
unscaled amplitude `printedEncoded` has squared norm two, ruling out its preparation from a
basis state by a matrix satisfying `star U * U = 1`. See [TerhalSmolin1998] for the source
development.

## Main statements

* `printed_nondegeneracy_false`: refutes the stated code nondegeneracy condition for this
  generator.
* `printedEncoded_norm_sq`: computes the unscaled encoded amplitude norm.
* `no_unitary_printed_preparation`: excludes the corresponding basis-state preparation.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.SingleQuery97.MainResults.Counters

/-- The binary length-two vector with both entries equal to one. -/
def generator : Fin 2 → ZMod 2 := ![1,1]

/-- Scalar multiplication of `generator` gives an injective encoding of a binary coefficient. -/
theorem coefficient_injective :
    Function.Injective (fun a : ZMod 2 => fun i => a * generator i) := by
  intro a b hab
  have h := congrFun hab 0
  simpa only [generator, Matrix.cons_val_zero, mul_one] using h

/-- The vector `generator` is nonzero. -/
theorem generator_nonzero : generator ≠ 0 := by
  intro h
  have hz := congrFun h 0
  norm_num [generator] at hz

/-- The singleton family consisting of `generator` is linearly independent over `ZMod 2`. See
[TerhalSmolin1998]. -/
theorem generator_linearIndependent :
    LinearIndependent (ZMod 2) (fun _ : Fin 1 => generator) := by
  rw [linearIndependent_unique_iff]
  exact generator_nonzero

/-- The binary dot product of `generator` with itself is zero. -/
theorem generator_self_dot : (∑ i : Fin 2, generator i * generator i) = 0 := by
  decide

/-- Every scalar multiple of `generator` has zero dot product with `generator`. -/
theorem code_dot_zero (a : ZMod 2) :
    (∑ i : Fin 2, (a * generator i) * generator i) = 0 := by
  have ht : (2 : ZMod 2) = 0 := by decide
  have ha : a+a = 0 := by
    calc a+a = (2 : ZMod 2)*a := by ring
         _ = 0 := by rw [ht,zero_mul]
  simpa [generator, Fin.sum_univ_two] using ha

/-- The code spanned by `generator` fails the condition that a codeword orthogonal to all
codewords must be zero. See [TerhalSmolin1998]. -/
theorem printed_nondegeneracy_false :
    ¬ (∀ c ∈ Set.range (fun a : ZMod 2 => fun i => a * generator i),
      (∀ a : ZMod 2, (∑ i : Fin 2, c i * (a * generator i)) = 0) → c = 0) := by
  intro h
  apply generator_nonzero
  apply h generator
  · exact ⟨1,by funext i; simp⟩
  · intro a
    simpa only [mul_comm (generator _)] using code_dot_zero a

/-- The joint basis of a one-bit coefficient register and a two-bit encoded register. -/
abbrev Basis := (Fin 1 → ZMod 2) × (Fin 2 → ZMod 2)

/-- The unscaled amplitude equal to one on coefficient-encoding pairs and zero on all other
joint basis elements. -/
def printedEncoded (p : Basis) : ℂ :=
  if p.2 = (fun i => p.1 0 * generator i) then 1 else 0

/-- The total squared norm of `printedEncoded` is two. -/
theorem printedEncoded_norm_sq :
    (∑ p : Basis, star (printedEncoded p) * printedEncoded p) = (2 : ℂ) := by
  rw [Fintype.sum_prod_type]
  simp [printedEncoded]

/-- The total squared norm of `printedEncoded` is not one. -/
theorem printedEncoded_not_normalized :
    (∑ p : Basis, star (printedEncoded p) * printedEncoded p) ≠ (1 : ℂ) := by
  rw [printedEncoded_norm_sq]
  norm_num

/-- If `star U * U = 1`, applying `U` to any basis vector cannot produce `printedEncoded`. See
[TerhalSmolin1998]. -/
theorem no_unitary_printed_preparation (U : Matrix Basis Basis ℂ)
    (hU : star U * U = 1) (b : Basis) :
    U.mulVec (Pi.single b 1) ≠ printedEncoded := by
  classical
  have hc : (∑ p : Basis, star (U p b) * U p b) = (1 : ℂ) := by
    have he := congrArg (fun M : Matrix Basis Basis ℂ => M b b) hU
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using he
  have hcol : U.mulVec (Pi.single b 1) = fun p => U p b := by
    funext p
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  intro he
  apply printedEncoded_not_normalized
  rw [← he,hcol]
  exact hc

end Qatlib.Papers.SingleQuery97.MainResults.Counters
