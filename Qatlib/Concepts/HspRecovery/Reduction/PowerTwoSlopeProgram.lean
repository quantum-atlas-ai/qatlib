/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.Reductions
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.SieveAlgorithm

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

def sourceParityTrials (n : ℕ) : ℕ := 1000 * (n + 1)

noncomputable def sourcePowerTwoQueryBudget : ℕ → ℕ
  | 0 => 0
  | n + 1 => sourceParityTrials (n + 1) *
      (24 * 2 ^ (3 * Nat.ceil (Real.sqrt n))) + sourcePowerTwoQueryBudget n

end Qatlib.Concepts.HspRecovery.ReductionCore
