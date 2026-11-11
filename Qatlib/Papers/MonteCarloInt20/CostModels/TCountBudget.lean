/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Reported leading T-count budgets

`tcountPrev` and `tcountNew` express the reported dominant T-gate costs for the sequential and
nested Monte Carlo methods of [KanekoEtAl2020]. The component definitions separate PRN updates,
PRN jumps, and inverse-CDF conversion.

The illustrative parameter choice gives exact integer costs, while `totalRatio` uses the rounded
per-operation factor 64 to compare total leading costs.

## Main statements

* `tcount_prev_eq`: expands the previous-method cost into its leading polynomial.
* `tcount_new_eq`: expands the nested-method cost under the reported jump-width convention.
* `perf_ratio_typical`: bounds the illustrative per-operation ratio between 63 and 64.
* `total_ratio_typical`: evaluates the rounded total-cost ratio.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MonteCarloInt20.CostModels.Reported

/-- The reported leading T-count `140 * n_prn ^ 2` for one self-updating PRN step. -/
def tcountSelfUpdate (n_prn : ℕ) : ℕ := 140 * n_prn ^ 2

/-- The reported leading T-count `105 * n_dig ^ 2 + 28 * n_dig * n_icdf` for one inverse-CDF
conversion. -/
def tcountConversion (n_dig n_icdf : ℕ) : ℕ := 105 * n_dig ^ 2 + 28 * n_dig * n_icdf

/-- The reported leading T-count for a PRN jump using `n_samp + n_obl` exponent bits. -/
def tcountJump (n_samp n_obl n_prn : ℕ) : ℕ := 140 * (n_samp + n_obl) * n_prn ^ 2

/-- The previous-method leading T-count, consisting of one self-update and two inverse-CDF
conversions. -/
def tcountPrev (n_prn n_dig n_icdf : ℕ) : ℕ :=
  tcountSelfUpdate n_prn + 2 * tcountConversion n_dig n_icdf

/-- The nested-method leading T-count, consisting of two PRN jumps and two inverse-CDF
conversions. -/
def tcountNew (n_samp n_obl n_prn n_dig n_icdf : ℕ) : ℕ :=
  2 * tcountJump n_samp n_obl n_prn + 2 * tcountConversion n_dig n_icdf

/-- The previous-method leading T-count expands to `140 * n_prn ^ 2 + 210 * n_dig ^ 2 + 56 *
n_dig * n_icdf` [KanekoEtAl2020]. -/
theorem tcount_prev_eq (n_prn n_dig n_icdf : ℕ) :
    tcountPrev n_prn n_dig n_icdf =
      140 * n_prn ^ 2 + 210 * n_dig ^ 2 + 56 * n_dig * n_icdf := by
  unfold tcountPrev tcountSelfUpdate tcountConversion
  ring

/-- The nested-method leading T-count expands to `280 * (n_samp + n_obl) * n_prn ^ 2 + 210 *
n_dig ^ 2 + 56 * n_dig * n_icdf`. -/
theorem tcount_new_eq (n_samp n_obl n_prn n_dig n_icdf : ℕ) :
    tcountNew n_samp n_obl n_prn n_dig n_icdf =
      280 * (n_samp + n_obl) * n_prn ^ 2 + 210 * n_dig ^ 2 + 56 * n_dig * n_icdf := by
  unfold tcountNew tcountJump tcountConversion
  ring

/-- The previous-method leading T-count at PRN width 64, digit width 16, and inverse-CDF
parameter 109. -/
def tcountPrevTypical : ℕ := tcountPrev 64 16 109

/-- The nested-method leading T-count with sample and coordinate widths 20, PRN width 64, digit
width 16, and inverse-CDF parameter 109. -/
def tcountNewTypical : ℕ := tcountNew 20 20 64 16 109

/-- The illustrative previous-method leading T-count is exactly 724864. -/
theorem tcount_prev_typical : tcountPrevTypical = 724864 := by
  unfold tcountPrevTypical tcountPrev tcountSelfUpdate tcountConversion
  norm_num

/-- The illustrative nested-method leading T-count is exactly 46026624. -/
theorem tcount_new_typical : tcountNewTypical = 46026624 := by
  unfold tcountNewTypical tcountNew tcountJump tcountConversion
  norm_num

/-- The illustrative previous-method leading T-count lies strictly between 710000 and 730000. -/
theorem tcount_prev_typical_magnitude :
    (710000 : ℝ) < (tcountPrevTypical : ℝ) ∧ (tcountPrevTypical : ℝ) < 730000 := by
  rw [tcount_prev_typical]; norm_num

/-- The illustrative nested-method leading T-count lies strictly between 46000000 and 47000000. -/
theorem tcount_new_typical_magnitude :
    (46000000 : ℝ) < (tcountNewTypical : ℝ) ∧ (tcountNewTypical : ℝ) < 47000000 := by
  rw [tcount_new_typical]; norm_num

/-- The illustrative nested-to-previous per-operation T-count ratio lies strictly between 63 and
64 [KanekoEtAl2020]. -/
theorem perf_ratio_typical :
    (63 : ℚ) < (tcountNewTypical : ℚ) / (tcountPrevTypical : ℚ) ∧
      (tcountNewTypical : ℚ) / (tcountPrevTypical : ℚ) < 64 := by
  rw [tcount_new_typical, tcount_prev_typical]
  norm_num

/-- The rounded leading total-cost ratio `64 * ((l * δrel)⁻¹ / D)`. -/
def totalRatio (l δrel D : ℝ) : ℝ := 64 * ((l * δrel)⁻¹ / D)

/-- The rounded total-cost ratio is below one exactly when `(l * δrel)⁻¹ / D` is below `1 / 64`. -/
theorem total_ratio_beneficial_iff (l δrel D : ℝ) : totalRatio l δrel D < 1 ↔ (l * δrel)⁻¹ / D < 1 / 64 := by
  unfold totalRatio
  constructor <;> intro h <;> nlinarith

/-- For `l = δrel = 1 / 100` and `D = 2 ^ 20`, the rounded total-cost ratio is exactly `625 /
1024` [KanekoEtAl2020]. -/
theorem total_ratio_typical :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) = 625 / 1024 := by
  unfold totalRatio
  norm_num

/-- The rounded total-cost ratio for the illustrative parameter choice is strictly below one. -/
theorem total_ratio_typical_lt_one :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) < 1 := by
  rw [total_ratio_typical]; norm_num

/-- The rounded total-cost ratio for the illustrative parameter choice is at most 0.64. -/
theorem total_ratio_typical_le_064 :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) ≤ 0.64 := by
  rw [total_ratio_typical]; norm_num

end Qatlib.Papers.MonteCarloInt20.CostModels.Reported
