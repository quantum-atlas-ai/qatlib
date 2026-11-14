/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

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
