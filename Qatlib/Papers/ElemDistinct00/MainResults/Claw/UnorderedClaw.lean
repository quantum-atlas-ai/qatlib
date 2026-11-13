/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Papers.ElemDistinct00.MainResults.Claw.OrReduction
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The unordered claw upper bound function

`clawQ2UpperFunction` records the piecewise scalar expression for unordered claw comparison
complexity. Its two branches are selected by whether `M ≤ N²`, and the module provides
simplification lemmas for each regime.

This defines a scalar function and proves its branch identities; it does not
prove `ClawQ2UpperBound clawQ2UpperFunction` or construct a claw algorithm.

The mathematical setting follows [BuhrmanEtAl2005].

## Main statements

* `clawQ2UpperFunction_of_le`: the `N^(1/2) * M^(1/4) * log N` branch.
* `clawQ2UpperFunction_of_gt`: the `sqrt M * log N` branch.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.Claw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- The piecewise cost expression `N^(1/2) * M^(1/4) * log N` when `M ≤ N²`, and `sqrt M * log
N` otherwise. -/
def clawQ2UpperFunction (N M : ℕ) : ℝ :=
  if M ≤ N ^ 2 then
    (N : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ)
  else
    Real.sqrt (M : ℝ) * Real.log (N : ℝ)

/-- When `M ≤ N²`, the defined cost expression is `N^(1/2) * M^(1/4) * log N`. -/
theorem clawQ2UpperFunction_of_le {N M : ℕ} (h : M ≤ N ^ 2) :
    clawQ2UpperFunction N M =
      (N : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ) := by
  unfold clawQ2UpperFunction
  rw [if_pos h]

/-- When `M > N²`, the defined cost expression is `sqrt M * log N`. -/
theorem clawQ2UpperFunction_of_gt {N M : ℕ} (h : ¬ M ≤ N ^ 2) :
    clawQ2UpperFunction N M = Real.sqrt (M : ℝ) * Real.log (N : ℝ) := by
  unfold clawQ2UpperFunction
  rw [if_neg h]

end Qatlib.Papers.ElemDistinct00.MainResults.Claw
