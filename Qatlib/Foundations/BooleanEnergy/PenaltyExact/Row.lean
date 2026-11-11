/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

/-!
# Boolean conjunction penalty identities

This module defines the conjunction penalty and the linear expression that replaces a product of
two spins using an ancillary bit. Exhaustive Boolean identities characterize zero penalty and
relate the square of the linear expression to eight times the penalty, providing the local
algebra for the reduction used with [SuksmonoMinato2019].

## Main statements

* `andPenalty_zero_iff`: Characterize correct ancillary bits.
* `rowLinear_square`: Relate the squared linear expression to the penalty.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.HadamardGram

/-- The Boolean conjunction penalty `3a + xy - 2xa - 2ya`, with Boolean inputs interpreted as
real bits. -/
def andPenalty (x y a : Bool) : ℝ :=
  3*bit a+bit x*bit y-2*bit x*bit a-2*bit y*bit a

/-- The linear expression `1 - 2x - 2y + 4a` in the real values of three Boolean bits. -/
def rowLinear (x y a : Bool) : ℝ := 1-2*bit x-2*bit y+4*bit a

/-- The Boolean conjunction penalty is nonnegative. -/
theorem andPenalty_nonneg (x y a : Bool) : 0 ≤ andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit]

/-- An ancillary bit unequal to the conjunction incurs penalty at least one; see
[SuksmonoMinato2019]. -/
theorem andPenalty_wrong (x y a : Bool) (h : a ≠ (x && y)) :
    1 ≤ andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit] at *

/-- The correct conjunction value gives zero penalty. -/
theorem andPenalty_correct (x y : Bool) : andPenalty x y (x && y) = 0 := by
  cases x <;> cases y <;> norm_num [andPenalty,bit]

/-- The conjunction penalty vanishes exactly when the ancillary bit equals the conjunction of
the main bits. -/
theorem andPenalty_zero_iff (x y a : Bool) : andPenalty x y a = 0 ↔ a = (x && y) := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit]

/-- With the correct ancillary bit, the rowwise linear expression equals the product of the two
spins. -/
theorem rowLinear_correct (x y : Bool) : rowLinear x y (x && y) = spin x*spin y := by
  cases x <;> cases y <;> norm_num [rowLinear,spin,bit]

/-- The square of the rowwise linear expression is one plus eight times the conjunction penalty. -/
theorem rowLinear_square (x y a : Bool) :
    rowLinear x y a ^ 2 = 1+8*andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [rowLinear,andPenalty,bit]

end Qatlib.Foundations.BooleanEnergy.PenaltyExact
