/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircApprox95.MainResults.MeasureBounds

/-!
# Fractions of finitely counted decision problems

The module turns an exponential upper bound on a natural-number count into an upper bound on its
fraction among 2ᵈ possibilities. `fraction_bound_of_count` isolates the exponent subtraction
used in decision and guessing problem counts. See [Knill1995].

## Main statements

* `fraction_bound_of_count`: converts a count bound 2ᴬ into a fraction bound 2ᴬ⁻ᵈ.

## References

* [Knill, 1995][Knill1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCircApprox95.MainResults

/-- If `count ≤ exp2 A`, then dividing the count by `2 ^ d` gives at most `exp2 (A - (d : ℝ))`.
This arithmetic step supports the counting bounds of Theorems 5.1 and 5.3 in [Knill1995]. -/
theorem fraction_bound_of_count (count d : ℕ) (A : ℝ)
    (hcount : (count : ℝ) ≤ exp2 A) :
    (count : ℝ) / (2 : ℝ) ^ d ≤ exp2 (A - (d : ℝ)) := by
  unfold exp2 at hcount ⊢
  change (count : ℝ) / (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (A - (d : ℝ))
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  exact div_le_div_of_nonneg_right hcount (by positivity)

end Qatlib.Papers.QCircApprox95.MainResults
