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
open Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

open Qatlib

def DlogGoodSamplingBudget : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → orderOf g = p - 1 → x = g ^ r → q ≤ 2 * (p - 1) →
    ∀ (hnorm : Normalized (dlogTwoDimState p q g x)),
    (dlogBornLaw p q g x hnorm).probEvent (L := 1)
        (fun ω => dlogGoodOutcome p q r (ω 0)) ≥ 1 / 480 ∧
    (∀ t : ℕ,
      (dlogBornLaw p q g x hnorm).probEvent (L := 1920 * 20 * t)
          (fun ω => dlogGoodCountGE p q r t (1920 * 20 * t) ω)
        ≥ 1 / 2)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
