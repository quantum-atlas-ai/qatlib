/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.CostModels.TCountBudget

/-!
# Corrected jump widths and leading cost ratios

This module defines corrected jump-index widths and recomputes the leading fee expressions used
to compare the Monte Carlo constructions of [KanekoEtAl2020]. The model retains the stated
multiplication and conversion fees while using the corrected index width.

The illustrative new-method fee is `47173504`, its per-step multiplier lies strictly between 65
and 66, and the specified total ratio is the exact rational `32905625 / 53018624`.

## Main statements

* `newFee_formula`: Expand the corrected leading fee for positive term-bit count.
* `corrected_example`: Evaluate the corrected illustrative fee.
* `total_example_below_one`: The specified total leading-cost ratio is below one.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MonteCarloInt20.CostModels.Corrected

/-- The jump-index width `sampleBits + termBits + 1`, with one further bit when `termBits = 0`. -/
def jumpIndexWidth (sampleBits termBits : ℕ) : ℕ :=
  sampleBits + termBits + 1 + if termBits = 0 then 1 else 0

/-- For positive `d`, the corrected jump-index width is `s + d + 1`. -/
theorem jumpIndexWidth_positive_terms (s d : ℕ) (hd : 0 < d) :
    jumpIndexWidth s d = s+d+1 := by simp [jumpIndexWidth, Nat.ne_of_gt hd]

/-- With zero term bits, the corrected jump-index width is `s + 2`; see [KanekoEtAl2020]. -/
theorem jumpIndexWidth_single_term (s : ℕ) : jumpIndexWidth s 0 = s+2 := by
  simp [jumpIndexWidth]

/-- The non-self-updating multiplication fee model `70 * rngBits^2`. -/
def nonselfFee (rngBits : ℕ) : ℕ := 70*rngBits^2

/-- The reported self-update fee is twice the modeled non-self-updating multiplication fee. -/
theorem reported_self_update_fee (n : ℕ) : Reported.tcountSelfUpdate n = 2*nonselfFee n := by
  simp [Reported.tcountSelfUpdate, nonselfFee]
  ring

/-- The jump fee obtained by charging two non-self-updating multiplications per corrected index
bit. -/
def jumpFee (s d n : ℕ) : ℕ := 2*jumpIndexWidth s d*nonselfFee n

/-- The corrected new-method fee consisting of two jump fees and two reported conversion fees. -/
def newFee (s d n p r : ℕ) : ℕ :=
  2*jumpFee s d n + 2*Reported.tcountConversion p r

/-- For positive `d`, the corrected fee expands to `280 * (s + d + 1) * n^2 + 210 * p^2 + 56 * p
* r`; see [KanekoEtAl2020]. -/
theorem newFee_formula (s d n p r : ℕ) (hd : 0 < d) :
    newFee s d n p r = 280*(s+d+1)*n^2+210*p^2+56*p*r := by
  simp only [newFee, jumpFee, jumpIndexWidth_positive_terms s d hd,
    nonselfFee, Reported.tcountConversion]
  ring

/-- The corrected fee at parameters `(20, 20, 64, 16, 109)` equals `47173504`; see
[KanekoEtAl2020]. -/
theorem corrected_example : newFee 20 20 64 16 109 = 47173504 := by
  norm_num [newFee, jumpFee, jumpIndexWidth, nonselfFee, Reported.tcountConversion]

/-- The real ratio of the corrected illustrative new-method fee to the reported typical
previous-method fee. -/
def exampleMultiplier : ℝ := (newFee 20 20 64 16 109 : ℝ) / (Reported.tcountPrevTypical : ℝ)

/-- The illustrative fee multiplier equals the exact rational `52649 / 809`. -/
theorem exampleMultiplier_exact : exampleMultiplier = 52649/809 := by
  rw [exampleMultiplier, corrected_example, Reported.tcount_prev_typical]
  norm_num

/-- The illustrative fee multiplier lies strictly between 65 and 66. -/
theorem exampleMultiplier_bounds : 65 < exampleMultiplier ∧ exampleMultiplier < 66 := by
  rw [exampleMultiplier_exact]
  norm_num

/-- The illustrative fee multiplier times the relative query factor `(scale * relativeError)⁻¹ /
dimensions`. -/
def totalRatio (scale relativeError dimensions : ℝ) : ℝ :=
  exampleMultiplier * ((scale*relativeError)⁻¹/dimensions)

/-- At scale and relative error one hundredth and dimension `2^20`, the total ratio is exactly
`32905625 / 53018624`; see [KanekoEtAl2020]. -/
theorem total_example : totalRatio (1/100) (1/100) (2^20) = 32905625/53018624 := by
  rw [totalRatio, exampleMultiplier_exact]
  norm_num

/-- At the specified illustrative parameters, the corrected total leading-cost ratio is strictly
less than one. -/
theorem total_example_below_one : totalRatio (1/100) (1/100) (2^20) < 1 := by
  rw [total_example]
  norm_num

end Qatlib.Papers.MonteCarloInt20.CostModels.Corrected
