/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# Rational interval operations and dyadic rounding

`Interval` stores rational endpoints, with `Valid`, `Contains`, `width`, and `radius` describing
its basic properties. `roundDown` and `rounded` implement floor rounding on a dyadic grid.

`add` and `mul` use endpoint arithmetic, while `divPositive` checks validity and a positive
lower denominator bound before forming a quotient enclosure. These operations support certified
numerical estimation, a setting motivated by [Montanaro2015].

## Main statements

* `rounded`: Dyadic interval around a rational input.
* `mul`: Endpoint enclosure for multiplication.
* `divPositive`: Optional division after validity and gap checks.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.IntervalArith.IntervalOps

/-- A pair of rational lower and upper endpoints, without an imposed ordering. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

/-- The condition that the lower endpoint is at most the upper endpoint. -/
def Valid (a : Interval) : Prop := a.lo ≤ a.hi
instance (a : Interval) : Decidable (Valid a) := inferInstanceAs (Decidable (a.lo ≤ a.hi))
/-- The predicate that a real number lies between the rational endpoints, inclusively. -/
def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)
/-- The upper endpoint minus the lower endpoint. -/
def width (a : Interval) : ℚ := a.hi-a.lo
/-- The maximum of the absolute values of the two endpoints. -/
def radius (a : Interval) : ℚ := max |a.lo| |a.hi|
/-- The rational dyadic mesh size `1 / 2^k`. -/
def unit (k : ℕ) : ℚ := 1/(2:ℚ)^k
/-- Rounds a rational number down to the dyadic grid of mesh size `1 / 2^k`. -/
def roundDown (q : ℚ) (k : ℕ) : ℚ := (⌊q*(2:ℚ)^k⌋ : ℤ)/(2:ℚ)^k
/-- The interval from the rounded-down dyadic endpoint to one mesh step above it. -/
def rounded (q : ℚ) (k : ℕ) : Interval := ⟨roundDown q k, roundDown q k+unit k⟩
/-- The interval obtained by adding corresponding lower and upper endpoints. -/
def add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩
/-- The interval whose endpoints are the minimum and maximum of the four endpoint products. -/
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
/-- Returns the product with the reciprocal denominator interval when both intervals are valid
and `0 < gap ≤ b.lo`; otherwise returns `none`. -/
def divPositive (a b : Interval) (gap : ℚ) : Option Interval :=
  if 0 < gap ∧ gap ≤ b.lo ∧ Valid a ∧ Valid b then some (mul a ⟨1/b.hi,1/b.lo⟩) else none

end Qatlib.Foundations.IntervalArith.IntervalOps
