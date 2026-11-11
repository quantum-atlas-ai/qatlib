/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Powers of two in the walk bounds

This module collects elementary identities for real powers of two used in the probability bounds
of [ChildsEtAl2003]. The lemmas combine exponents, simplify the square of `2^(x/6)`, and relate
natural powers to real powers.

## Main statements

* `two_rpow_add`: multiplication of real powers of two.
* `sq_two_rpow_sixth`: the square identity for the sixth-exponent scale.
* `two_pow_eq_two_rpow`: agreement of natural and real exponents.

## References

* [Childs et al., 2003][ChildsEtAl2003]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith

/-- The product of two real powers of two is the real power of two with the sum of their
exponents. -/
lemma two_rpow_add (a b : ℝ) : (2 : ℝ) ^ a * (2 : ℝ) ^ b = (2 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

/-- The real number four equals the real power of two with exponent two. -/
lemma four_eq_two_rpow_two : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
  rw [Real.rpow_two]
  norm_num

/-- The square of the real power `2^(x/6)` equals `2^(x/3)`. -/
lemma sq_two_rpow_sixth (x : ℝ) : ((2 : ℝ) ^ (x / 6)) ^ 2 = (2 : ℝ) ^ (x / 3) := by
  rw [show ((2 : ℝ) ^ (x / 6)) ^ 2 = ((2 : ℝ) ^ (x / 6)) ^ (2 : ℝ) from
    (Real.rpow_natCast ((2 : ℝ) ^ (x / 6)) 2).symm]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (x / 6) 2]
  rw [show x / 6 * 2 = x / 3 by ring]

/-- For a natural exponent, the natural power of two equals the real power of two with the cast
exponent. -/
lemma two_pow_eq_two_rpow (n : ℕ) : (2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ)) :=
  (Real.rpow_natCast 2 n).symm

end Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith
