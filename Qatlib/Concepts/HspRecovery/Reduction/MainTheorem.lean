/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthDihe
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore.MainTheorem

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.SieveAlgorithm

theorem theorem11_query_growth :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (n : ℝ)) :=
  sourceDescentQueryGrowth

theorem theorem11_powerTwo_parity_recovery :
    DihedralSieveAlgorithm :=
  dihedralSieveAlgorithm

theorem theorem11_powerTwo_instance :
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (n : ℝ))) ∧
    DihedralSieveAlgorithm :=
  ⟨theorem11_query_growth, theorem11_powerTwo_parity_recovery⟩

end Qatlib.Concepts.HspRecovery.ReductionCore.MainTheorem
