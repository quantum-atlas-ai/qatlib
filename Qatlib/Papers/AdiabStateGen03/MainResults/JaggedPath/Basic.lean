/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath.ProjectionGap
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar gap identities for jagged paths

Establishes the completed-square identity for the scalar gap expression used in jagged
interpolation paths. The midpoint value equals the nonnegative overlap parameter, and the gap is
bounded below by that parameter throughout the interpolation interval. See [AharonovTaShma2007].

## Main statements

* `gap_completed_square`: Rewrites the squared gap as the overlap square plus a nonnegative
  correction.
* `gap_ge_half`: Bounds the scalar gap below by the overlap parameter.
* `slowlyVarying_overlap_nonneg`: Consecutive square-root weight sums are nonnegative.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath

open Qatlib.Papers.AdiabStateGen03.MainResults

/-- For nonnegative `r`, the scalar gap expression at interpolation parameter one half equals
`r` [AharonovTaShma2007]. -/
theorem gap_half_eq {r : ℝ} (hr0 : 0 ≤ r) :
    Real.sqrt (1 - 4 * (1 - 1 / 2) * (1 / 2) * (1 - r ^ 2)) = r := by
  have h : 1 - 4 * (1 - 1 / 2) * (1 / 2) * (1 - r ^ 2) = r ^ 2 := by ring
  rw [h, Real.sqrt_sq hr0]

/-- The squared-gap expression equals `r ^ 2 + (1 - 2 * η) ^ 2 * (1 - r ^ 2)`
[AharonovTaShma2007]. -/
theorem gap_completed_square (η r : ℝ) :
    1 - 4 * (1 - η) * η * (1 - r ^ 2) = r ^ 2 + (1 - 2 * η) ^ 2 * (1 - r ^ 2) := by
  ring

/-- For `0 ≤ η ≤ 1` and `0 ≤ r ≤ 1`, the scalar gap expression is at least `r`
[AharonovTaShma2007]. -/
theorem gap_ge_half {η r : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ≤ Real.sqrt (1 - 4 * (1 - η) * η * (1 - r ^ 2)) :=
  overlap_le_sqrt_gap hη0 hη1 hr0 hr1

/-- The sum of square roots of products of consecutive weights is nonnegative. -/
theorem slowlyVarying_overlap_nonneg {n T : ℕ} (π : Fin (T + 1) → Dim n → ℝ)
    (t : Fin T) :
    0 ≤ ∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i) :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

end Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath
