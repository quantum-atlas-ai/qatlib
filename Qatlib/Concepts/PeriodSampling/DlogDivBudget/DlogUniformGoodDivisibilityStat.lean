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
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib

def DlogUniformGoodDivisibility : Prop :=
  ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    ∀ w : ℕ, 2 ≤ w → w ∣ p - 1 →
      (dlogUniformGoodLaw p q).probEvent (L := 1)
          (fun ω => (w : ℤ) ∣ dlogCprime p q (ω 0).val)
        * ((q / 12 : ℕ) : ℝ) ≤ (((p - 1) / w + 1 : ℕ) : ℝ)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
