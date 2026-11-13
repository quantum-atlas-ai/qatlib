/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayStat
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonDefs

/-!
# Classical stopping comparison statement

`SzegedyClassicalStopComparison` formulates the classical detection guarantee from a
symmetric-chain gap and a marked-fraction bound. It includes a zero-success implication for an
empty marked set and a constant lower bound after the prescribed number of steps. See
[Szegedy2004] for the mathematical background.

## Main statements

* `SzegedyClassicalStopComparison`: the classical detection proposition.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

/-- The proposition that the stated gap and marked-fraction assumptions yield zero success for
an empty marked set and success at least `1 / 32` whenever `K ≥ 1000 / (δ * ε)`. -/
def SzegedyClassicalStopComparison : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I→I→ℝ) (S : Finset I) (δ ε : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ → 0 < ε → ε ≤ markedFraction S →
    (S = ∅ → ∀ K : ℕ, classicalDetectSuccess P S K = 0) ∧
    ∀ K : ℕ, (1000/(δ*ε) ≤ (K:ℝ)) → (1/32:ℝ) ≤ classicalDetectSuccess P S K

end Qatlib.Concepts.WalkSearch.ClassicalStop
