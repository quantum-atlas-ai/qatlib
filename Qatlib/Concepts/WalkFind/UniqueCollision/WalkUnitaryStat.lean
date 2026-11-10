/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk
set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

def WalkUnitary : Prop :=
  ∀ (k N r : ℕ), k ≤ N - r → k ≤ r + 1 →
    (star (jwStep1 k N r) * jwStep1 k N r) = 1 ∧
    (star (jwStep2 k r) * jwStep2 k r) = 1 ∧
    (star (jwWalk k N r) * jwWalk k N r) = 1 ∧
    (∀ i j, (jwWalk k N r i j).im = 0)

end Qatlib.Concepts.WalkFind.UniqueCollision
