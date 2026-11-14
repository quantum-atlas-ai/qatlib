/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.MeasureTheory.OuterMeasure.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core

@[expose] public section

/-!
# A counterexample to the printed random-code collision law

This module enumerates independent pairs of binary rows of length three and evaluates a
particular response collision. The law `sampleLaw` has collision probability `1/7`, whereas the
printed expression in [TerhalSmolin1998] gives `1/4` for these parameters, as formalized by
`sampleLaw_not_printed_probability`.

## Main statements

* `sampleLaw_collision`: Under `sampleLaw`, the zero database and the unit vector at coordinate
  `2` have equal responses with probability `1/7`.
* `sampleLaw_not_printed_probability`: The collision probability for uniform independent binary
  rows is not `1/4`, providing a finite counterexample to the printed probability in
  [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomLawCounter

/-- The type of two-row binary matrices with three columns. -/
abbrev Rows := Fin 2 → Fin 3 → ZMod 2

/-- The property that both binary rows are nonzero and distinct. -/
def independentRows (g : Rows) : Prop := g 0 ≠ 0 ∧ g 1 ≠ 0 ∧ g 0 ≠ g 1

instance (g : Rows) : Decidable (independentRows g) := inferInstanceAs
  (Decidable (g 0 ≠ 0 ∧ g 1 ≠ 0 ∧ g 0 ≠ g 1))

/-- The finite set of two-row binary matrices whose rows are nonzero and distinct. -/
def samples : Finset Rows := Finset.univ.filter independentRows

/-- The property that both rows vanish in coordinate `2`. -/
def collides (g : Rows) : Prop := g 0 2 = 0 ∧ g 1 2 = 0

instance (g : Rows) : Decidable (collides g) := inferInstanceAs
  (Decidable (g 0 2 = 0 ∧ g 1 2 = 0))

/-- Every matrix in `samples` has linearly independent rows over `ZMod 2`. -/
theorem samples_linearIndependent (g : Rows) (hg : g ∈ samples) :
    LinearIndependent (ZMod 2) g := by
  have h := (Finset.mem_filter.mp hg).2
  rw [linearIndependent_fin2]
  refine ⟨h.2.1, ?_⟩
  intro a
  have ha : a = 0 ∨ a = 1 := by
    have hv := a.val_lt
    interval_cases hval : a.val
    · left; exact ZMod.val_injective 2 (by rw [hval]; decide)
    · right; exact ZMod.val_injective 2 (by rw [hval]; decide)
  rcases ha with rfl | rfl
  · simpa only [zero_smul, ne_eq, eq_comm] using h.1
  · simpa only [one_smul, ne_eq, eq_comm] using h.2.2

/-- There are exactly `42` matrices in `samples`. -/
theorem samples_card : samples.card = 42 := by decide

/-- Exactly `6` matrices in `samples` satisfy `collides`. -/
theorem collisions_card : (samples.filter collides).card = 6 := by decide

/-- The fraction of sampled matrices satisfying the collision condition is `1/7`. -/
theorem actual_collision_fraction :
    ((samples.filter collides).card : ℚ) / samples.card = 1/7 := by
  rw [samples_card, collisions_card]
  norm_num

/-- The enumerated collision fraction differs from the printed collision expression evaluated at
alphabet size `2`, code length `2`, and two candidates. -/
theorem printed_probability_false :
    ((samples.filter collides).card : ℚ) / samples.card ≠
      1 - (1 - (2:ℚ)^(-(2:ℤ)))^(2-1:ℕ) := by
  rw [actual_collision_fraction]
  norm_num

/-- The binary response vector obtained by taking the dot product of each row of `g` with `y`. -/
def code (g : Rows) (y : Fin 3 → ZMod 2) : Fin 2 → ZMod 2 :=
  fun i => ∑ j, g i j * y j

/-- The coordinate-vanishing collision condition is equivalent to equal responses for the zero
vector and the unit vector at coordinate `2`. -/
theorem collides_iff_response_equal (g : Rows) :
    collides g ↔ code g 0 = code g (Pi.single 2 1) := by
  have h0 : code g 0 = 0 := by funext i; simp [code]
  have h1 : code g (Pi.single 2 1) = fun i => g i 2 := by
    funext i
    simp [code, Pi.single_apply, mul_ite]
  rw [h0, h1]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h.1.symm
    · exact h.2.symm
  · intro h
    exact ⟨(congrFun h 0).symm, (congrFun h 1).symm⟩

/-- The two selected databases are distinct, the code length is `Nat.log 2 2 + 1`, and this
length is smaller than the database dimension. -/
theorem admissible_parameters :
    (0 : Fin 3 → ZMod 2) ≠ Pi.single 2 1 ∧
    (2:ℕ) = Nat.log 2 2 + 1 ∧ (2:ℕ) < 3 := by decide

/-- The uniform probability distribution on the finite set `samples`. -/
noncomputable def sampleLaw : PMF Rows :=
  PMF.uniformOfFinset samples (Finset.card_pos.mp (by rw [samples_card]; decide))

/-- Under `sampleLaw`, the zero database and the unit vector at coordinate `2` have equal
responses with probability `1/7`. -/
theorem sampleLaw_collision :
    sampleLaw.toOuterMeasure {g | code g 0 = code g (Pi.single 2 1)} =
      (1:ENNReal)/7 := by
  have he : {g | code g 0 = code g (Pi.single 2 1)} = {g | collides g} := by
    ext g
    exact (collides_iff_response_equal g).symm
  rw [he, sampleLaw, PMF.toOuterMeasure_uniformOfFinset'_apply]
  simp only [Set.mem_ofPred_eq]
  rw [samples_card, collisions_card]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- The collision probability for uniform independent binary rows is not `1/4`, providing a
finite counterexample to the printed probability in [TerhalSmolin1998]. -/
theorem sampleLaw_not_printed_probability :
    sampleLaw.toOuterMeasure {g | code g 0 = code g (Pi.single 2 1)} ≠
      (1:ENNReal)/4 := by
  rw [sampleLaw_collision]
  norm_num

end Qatlib.Papers.SingleQuery97.MainResults.RandomLawCounter
