/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

def QueryComplexity : Prop :=
  ∀ (k N : ℕ), 1 ≤ k →
    ((32 * Real.pi ^ 2 * ((k : ℝ) ^ 3) * (2 ^ (k + 4)) * (k + 1) * k) ^ (k + 1) : ℝ) ≤ N →
    ∀ (I : Finset (Fin N)), I.card = k →
      let r := Nat.floor ((N : ℝ) ^ ((k : ℝ) / (k + 1)))
      ∃ (t1 : ℕ),
        ((r + 2 * t1 * jwT2 k r : ℕ) : ℝ) ≤
          (1 + 16 * (Real.sqrt 2 * Real.pi / 6 + 1) * 3 * Real.pi *
              Real.sqrt ((k : ℝ)) / ((Real.pi - 1) * Real.pi - 3) *
              (2 : ℝ) ^ (k : ℝ)) *
            (N : ℝ) ^ ((k : ℝ) / (k + 1)) ∧
        jwEpsArc k r ^ 3 / 1000 ≤
          ‖jwMarkedAmplitude k N r t1 (jwT2 k r) I‖

end Qatlib.Concepts.WalkFind.UniqueCollision
