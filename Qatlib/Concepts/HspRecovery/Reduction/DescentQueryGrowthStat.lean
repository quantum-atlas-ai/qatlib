/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

def SourceDescentQueryGrowth : Prop := by
  classical
  exact
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
    (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt n)

end Qatlib.Concepts.HspRecovery.ReductionCore
