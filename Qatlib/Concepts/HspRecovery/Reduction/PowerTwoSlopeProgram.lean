/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.Reductions
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe

/-!
# Query budgets for recursive slope recovery

This module defines the repetition schedule and recursive query budget for recovering a dihedral
slope over a power-of-two modulus. `sourcePowerTwoQueryBudget` accumulates the cost of parity
trials at successive descent levels, using the sieve scale associated with [Kuperberg2005].

## Main definitions

* `sourceParityTrials`: the schedule `1000 * (n + 1)`.
* `sourcePowerTwoQueryBudget`: the sum of level costs, with zero cost at level zero.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.SieveAlgorithm

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The number `1000 * (n + 1)` of parity trials assigned to level `n`. -/
def sourceParityTrials (n : ℕ) : ℕ := 1000 * (n + 1)

/-- The recursive query budget with value zero at level zero and successor increment
`sourceParityTrials (n + 1) * (24 * 2 ^ (3 * Nat.ceil (Real.sqrt n)))`. -/
noncomputable def sourcePowerTwoQueryBudget : ℕ → ℕ
  | 0 => 0
  | n + 1 => sourceParityTrials (n + 1) *
      (24 * 2 ^ (3 * Nat.ceil (Real.sqrt n))) + sourcePowerTwoQueryBudget n

end Qatlib.Concepts.HspRecovery.ReductionCore
