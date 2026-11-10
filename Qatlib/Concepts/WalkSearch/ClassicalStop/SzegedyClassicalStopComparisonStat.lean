/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayStat
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonDefs
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

def SzegedyClassicalStopComparison : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I→I→ℝ) (S : Finset I) (δ ε : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ → 0 < ε → ε ≤ markedFraction S →
    (S = ∅ → ∀ K : ℕ, classicalDetectSuccess P S K = 0) ∧
    ∀ K : ℕ, (1000/(δ*ε) ≤ (K:ℝ)) → (1/32:ℝ) ≤ classicalDetectSuccess P S K

end Qatlib.Concepts.WalkSearch.ClassicalStop
