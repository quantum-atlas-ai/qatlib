/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parameters for multiscale phase readout

`bisectRange` defines the largest power-access index for a given number of bisection levels. The
module verifies the resulting range size and positivity of the associated dyadic precision. The
development follows [Kitaev1995].

## Main statements

* `bisectRange_succ`: identifies the range size as `2 ^ l`.
* `bisectPrecision_pos`: proves positivity of `2 ^ (-l - 2)`.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

/-- The maximal power index `2 ^ l - 1` for `l` bisection levels. -/
def bisectRange (l : ℕ) : ℕ := 2 ^ l - 1

/-- Adding one to the maximal bisection power index gives `2 ^ l`, as used in [Kitaev1995]. -/
theorem bisectRange_succ (l : ℕ) : bisectRange l + 1 = 2 ^ l := by
  unfold bisectRange
  have h : 0 < 2 ^ l := by positivity
  omega

/-- The bisection precision `2 ^ (-l - 2)` is strictly positive. -/
theorem bisectPrecision_pos (l : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(l : ℤ) - 2) := by
  positivity

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
