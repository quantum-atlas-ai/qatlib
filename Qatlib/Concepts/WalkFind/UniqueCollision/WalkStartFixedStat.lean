/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Fixed starting-state specification

`WalkStartFixed` states that the reduced Johnson walk fixes `jwStart` when `1 ≤ k ≤ r` and `k <
N-r`. This is the stationary starting-vector property used in the spectral analysis of collision
search [Ambainis2007ElementDistinctness].

## Main statements

* `WalkStartFixed`: the reduced starting-vector fixed-point proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

/-- The proposition that `jwWalk` fixes `jwStart` whenever `1 ≤ k ≤ r` and `k < N-r`. -/
def WalkStartFixed : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → k < N - r →
    jwWalk k N r *ᵥ jwStart k N r = jwStart k N r

end Qatlib.Concepts.WalkFind.UniqueCollision
