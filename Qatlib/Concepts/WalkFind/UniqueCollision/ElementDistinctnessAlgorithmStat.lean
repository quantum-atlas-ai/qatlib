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

def ElementDistinctnessAlgorithm : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → 2 * k ≤ r + 1 →
    ((8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) * (k + 1) * k : ℝ) ≤
      N - r) →
    ∀ (I : Finset (Fin N)), I.card = k →
      ∃ (t1 : ℕ),
        (t1 : ℝ) ≤ 8 / (jwEpsArc k r * jwAlpha k N r) ∧
        jwEpsArc k r ^ 3 / 1000 ≤
          ‖jwMarkedAmplitude k N r t1 (jwT2 k r) I‖ ∧
        (((r + 2 * t1 * jwT2 k r : ℕ) : ℝ)) ≤
          (r : ℝ) + 16 * (jwT2 k r : ℝ) / (jwEpsArc k r * jwAlpha k N r)

end Qatlib.Concepts.WalkFind.UniqueCollision
