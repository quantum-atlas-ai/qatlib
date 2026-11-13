/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.StatDistance

/-!
# Square-root distance bounds for statistical reduction

This module supplies elementary probability estimates for the statistical zero-knowledge
reduction. The theorem `sum_sq_sub_sqrt_le_of_tv` bounds the squared distance of square-root
amplitudes using total variation, and `sum_sq_sqrt` records their normalization. The
mathematical context is [AharonovTaShma2007].

## Main statements

* `sum_sq_sub_sqrt_le_of_tv`: If two probability distributions have total variation distance at
  most `ε`, the sum of squared differences of their square-root amplitudes is at most `2 * ε`.
* `sum_sq_sqrt`: The sum of squared square-root amplitudes of a nonnegative normalized
  distribution equals one.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.SZKReduction

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- If two probability distributions have total variation distance at most `ε`, the sum of
squared differences of their square-root amplitudes is at most `2 * ε` [AharonovTaShma2007]. -/
theorem sum_sq_sub_sqrt_le_of_tv (p q : Dim n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) (ε : ℝ)
    (hε : (1 / 2) * ∑ i, |p i - q i| ≤ ε) :
    ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 ≤ 2 * ε := by
  rw [StatDistance.sum_sq_sub_sqrt p q hp hq hp1 hq1]
  have hov := StatDistance.one_sub_tv_le_overlap p q hp hq hp1 hq1
  nlinarith

/-- The sum of squared square-root amplitudes of a nonnegative normalized distribution equals
one [AharonovTaShma2007]. -/
theorem sum_sq_sqrt (p : Dim n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, Real.sqrt (p i) ^ 2 = 1 := by
  rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hp i)), hp1]

end Qatlib.Papers.AdiabStateGen03.MainResults.SZKReduction
