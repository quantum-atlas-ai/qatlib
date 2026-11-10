/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.SignedOrbit
import Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
import Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
import Qatlib.Papers.ManyBodyFermi97.MainResults.MemoryComparison
import Qatlib.Papers.ManyBodyFermi97.MainResults.SecondQuantizedHubbard
import Qatlib.Papers.ManyBodyFermi97.MainResults.Antisymmetrization
import Qatlib.Papers.ManyBodyFermi97.MainResults.FirstQuantizedOperators
import Qatlib.Papers.ManyBodyFermi97.MainResults.FirstQuantizedHubbard
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

theorem proposed_budget_arithmetic {n m q : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (secondQuantizedBits m = m ∧
        firstQuantizedBits n m = n * quWordBits m ∧
        m ^ n ≤ 2 ^ firstQuantizedBits n m) ∧
      secondQuantHubbardCost m (chainPairs m) ≤ 10 * m ^ 2 ∧
      antisymTotalCost n q ≤ 4 * n ^ 2 * q ^ 2 ∧
      oneParticleStepCost m + twoParticleStepCost m ≤ 2 * m ^ 4 ∧
      firstQuantHubbardStepCost q ≤ 14 * q ^ 2 :=
  ⟨⟨rfl, rfl, firstQuantized_bits_suffice n m⟩, chain_hubbard_quadratic m hm,
    antisymTotalCost_bound hn hq, firstQuantized_simulation_bound hm,
    firstQuantHubbardStepCost_bound hq⟩

end Qatlib.Papers.ManyBodyFermi97.MainResults
