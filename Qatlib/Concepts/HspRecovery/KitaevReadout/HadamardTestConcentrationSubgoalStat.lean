/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest

/-!
# Specification of Hadamard test concentration

`HadamardTestConcentrationSubgoal` specifies a deviation bound for averages of independent
Hadamard test bits. It requires at least `log (2 / ε) / (2 * τ^2)` samples to bound the
probability of deviation at least `τ` from the cosine-dependent mean by `ε`, as needed for phase
readout in [Kitaev1995].

## Main statements

* `HadamardTestConcentrationSubgoal`: the sample-size and deviation guarantee.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

/-- Specifies that the average of independent Hadamard bits deviates from `(1 - cos (2πφ)) / 2`
by at least `τ` with probability at most `ε` under the stated sample-size condition. -/
def HadamardTestConcentrationSubgoal : Prop :=
  ∀ (φ : ℝ) (s : ℕ) (τ ε : ℝ), 0 < τ → 0 < ε → ε < 1 →
    Real.log (2 / ε) / (2 * τ ^ 2) ≤ s →
    (hadamardBitDist φ).probEvent (L := s)
        (fun ω => τ ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun b => if b then (1 : ℝ) else 0) ω
          - (1 - Real.cos (2 * Real.pi * φ)) / 2|)
      ≤ ε

end Qatlib.Concepts.HspRecovery.KitaevReadout
