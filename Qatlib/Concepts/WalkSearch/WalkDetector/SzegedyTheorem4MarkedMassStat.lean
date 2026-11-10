/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS
set_option warningAsError false

open Matrix

open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.WalkSearch.WalkDetector

def SzegedyTheorem4MarkedMass : Prop :=
  ∀ (n : ℕ) (f : Fin n → Bool),
    0 < n → (∃ i, f i = true) →
    (1 / (n : ℝ)) ≤ markedFraction (Finset.univ.filter (fun i => f i = true))

end Qatlib.Concepts.WalkSearch.WalkDetector
