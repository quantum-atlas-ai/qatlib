/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest
set_option warningAsError false

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

def HadamardTestConcentrationSubgoal : Prop :=
  ∀ (φ : ℝ) (s : ℕ) (τ ε : ℝ), 0 < τ → 0 < ε → ε < 1 →
    Real.log (2 / ε) / (2 * τ ^ 2) ≤ s →
    (hadamardBitDist φ).probEvent (L := s)
        (fun ω => τ ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun b => if b then (1 : ℝ) else 0) ω
          - (1 - Real.cos (2 * Real.pi * φ)) / 2|)
      ≤ ε

end Qatlib.Concepts.HspRecovery.KitaevReadout
