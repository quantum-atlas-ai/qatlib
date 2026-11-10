/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircApprox95.MainResults.MeasureBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCircApprox95.MainResults

theorem fraction_bound_of_count (count d : ℕ) (A : ℝ)
    (hcount : (count : ℝ) ≤ exp2 A) :
    (count : ℝ) / (2 : ℝ) ^ d ≤ exp2 (A - (d : ℝ)) := by
  unfold exp2 at hcount ⊢
  change (count : ℝ) / (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (A - (d : ℝ))
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  exact div_le_div_of_nonneg_right hcount (by positivity)

end Qatlib.Papers.QCircApprox95.MainResults
