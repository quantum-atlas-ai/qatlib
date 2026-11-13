/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Johnson-walk unitarity specification

`WalkUnitary` requires identity Gram matrices for both reduced diffusion steps and their
product, together with real entries for the walk. The proposition retains the size conditions `k
≤ N-r` and `k ≤ r+1` needed for the Johnson-walk reduction [Ambainis2007ElementDistinctness].

## Main statements

* `WalkUnitary`: the conditional unitarity and reality proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

/-- The proposition that both reduced diffusion steps and their product have identity Gram
matrices and the walk is real whenever `k ≤ N-r` and `k ≤ r+1`. -/
def WalkUnitary : Prop :=
  ∀ (k N r : ℕ), k ≤ N - r → k ≤ r + 1 →
    (star (jwStep1 k N r) * jwStep1 k N r) = 1 ∧
    (star (jwStep2 k r) * jwStep2 k r) = 1 ∧
    (star (jwWalk k N r) * jwWalk k N r) = 1 ∧
    (∀ i j, (jwWalk k N r i j).im = 0)

end Qatlib.Concepts.WalkFind.UniqueCollision
