/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib

def DlogTSampleTail : Prop :=
  ∀ (p q t : ℕ) [NeZero p] [NeZero q], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q)
      ≤ ∑ w ∈ (Nat.divisors (p - 1)).filter
            (fun w => dlogIsPrimePower w ∧ 18 < w),
          ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t ∧
    (12 ≤ t →
      (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q)
        < 1 / 2)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
