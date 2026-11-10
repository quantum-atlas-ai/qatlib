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

def WalkStartFixed : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → k < N - r →
    jwWalk k N r *ᵥ jwStart k N r = jwStart k N r

end Qatlib.Concepts.WalkFind.UniqueCollision
