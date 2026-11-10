/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
set_option warningAsError false
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.CollisionSearch

def RealExponentTransport : Prop :=
  ∀ (kcs : KCollisionSolver), 1 ≤ kcs.κ →
  ∀ (n k r s u c : ℕ) (R : (Fin k → Fin n) → Bool) (ρ : kcs.seed),
    1 ≤ r → r ≤ n →
    (kcs.cost r R s u c ρ : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
        ((s : ℝ) + ((n : ℝ) / r) ^ ((k : ℝ) / 2) *
          ((c : ℝ) + (Nat.sqrt r : ℝ) * (u : ℝ)))

end Qatlib.Concepts.WalkSearch.CollisionSearch
