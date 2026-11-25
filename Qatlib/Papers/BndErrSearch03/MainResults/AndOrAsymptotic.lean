/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Qatlib.Papers.BndErrSearch03.MainResults.AndOrTreeQueryCost

@[expose] public section

/-!
# Fixed-depth AND–OR cost

Section 4 gives a factor of c at each recursion depth and a square-root
base cost. At any fixed positive depth the resulting power of c is a
constant in the norm bound, which gives Big-O as the input size grows.
The declaration concerns the scalar recurrence.
-/

set_option autoImplicit false

open Qatlib.Papers.BndErrSearch03.MainResults.AndOrTreeQueryCost

namespace Qatlib.Papers.BndErrSearch03.MainResults

/-- For fixed positive depth, the scalar query-cost recurrence in Section 4
is bounded in norm by a fixed multiple of the square root of input size. -/
theorem andOr_cost_isBigO (c : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    Asymptotics.IsBigO Filter.atTop (fun N : ℝ => andOrCost c N (d - 1)) Real.sqrt := by
  refine Asymptotics.IsBigO.of_bound (‖c ^ (d - 1)‖) (Filter.Eventually.of_forall ?_)
  intro N
  rw [andOr_cost_depth c N d hd, norm_mul]

end Qatlib.Papers.BndErrSearch03.MainResults
