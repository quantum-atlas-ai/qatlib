/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPrimality95.MainResults

open scoped BigOperators

noncomputable def basicCost (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 3 * (Real.log (Real.log (N : ℝ))) ^ 2 *
    Real.log (Real.log (Real.log (N : ℝ)))

noncomputable def mainCost (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 3 * Real.log (Real.log (N : ℝ)) *
    Real.log (Real.log (Real.log (N : ℝ)))

end Qatlib.Papers.QPrimality95.MainResults
