/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

theorem quantumPropagator_zero (n : ℕ) (γ : ℝ) :
    quantumPropagator n γ 0 = 1 := by
  simp [quantumPropagator]

end Qatlib.Papers.QWalkDiff01.MainResults
