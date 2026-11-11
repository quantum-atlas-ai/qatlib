/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — bars-and-stripes reconstruction error (c005)

Fixed source: arXiv:1609.02542, Sec. IV B.2 on p.9.

On the `7 × 6` bars-and-stripes data set the paper blacks out a `5 × 4` block
(20 of the 42 pixels, about 47.6% of each test picture) and reconstructs it with
the trained model.  The average number of mistaken pixels per reconstruction is
reported as 10.45 after one iteration, 3.73 after 100, 0.59 after 1000, and
0.13 at the end of training (3850 iterations), i.e. 0.65% of the 20 corrupted
pixels.

The counts are measured empirically and are inputs here; the theorem proves the
exact rational arithmetic relating the reported mistakes to percentages and the
strict monotone decrease, and checks the reported 47.6% corruption figure.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Mistake rate per reconstruction: expected incorrect pixels divided by the
number of corrupted pixels. -/
def mistakeRate (mistakes : ℚ) (corrupted : ℕ) : ℚ := mistakes / corrupted

/-- c005 of p.9.  With a `5 × 4` block inside a `7 × 6` picture (20 of 42
pixels, 47.6% up to the paper's rounding), the measured mistakes per
reconstruction decrease strictly from 10.45 to 3.73, 0.59 and 0.13, and the
final rate is exactly 0.65% of the 20 corrupted pixels. -/
theorem reconstruction_error_decay :
    (5 * 4 : ℕ) = 20 ∧ (7 * 6 : ℕ) = 42 ∧
    |(20 : ℚ) / 42 * 100 - 476 / 10| < 1 / 50 ∧
    mistakeRate (1045 / 100) 20 = 209 / 400 ∧
    mistakeRate (373 / 100) 20 = 373 / 2000 ∧
    mistakeRate (59 / 100) 20 = 59 / 2000 ∧
    mistakeRate (13 / 100) 20 = 13 / 2000 ∧
    mistakeRate (1045 / 100) 20 * 100 = 209 / 4 ∧
    mistakeRate (373 / 100) 20 * 100 = 373 / 20 ∧
    mistakeRate (59 / 100) 20 * 100 = 59 / 20 ∧
    mistakeRate (13 / 100) 20 * 100 = 13 / 20 ∧
    mistakeRate (13 / 100) 20 = 65 / 10000 ∧
    (1045 / 100 : ℚ) > 373 / 100 ∧
    (373 / 100 : ℚ) > 59 / 100 ∧
    (59 / 100 : ℚ) > 13 / 100 := by
  unfold mistakeRate
  norm_num

end Qatlib.Papers.QAssistedPGM16.MainResults
