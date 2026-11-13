/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Real-exponent collision cost statement

`RealExponentTransport` states a real-valued cost bound for each seed of a supplied
`KCollisionSolver`. It uses the real quotient `n / r` and exponent `k / 2`, with the solver's
logarithmic overhead and natural square root retained explicitly. See [Ambainis2005] for the
mathematical background.

## Main statements

* `RealExponentTransport`: the real-valued collision cost proposition.

## References

* [Ambainis, 2005][Ambainis2005]
-/

open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.CollisionSearch

/-- The proposition that every supplied collision solver with `κ ≥ 1` satisfies the displayed
real-exponent cost bound for all seeds when `1 ≤ r ≤ n`. -/
def RealExponentTransport : Prop :=
  ∀ (kcs : KCollisionSolver), 1 ≤ kcs.κ →
  ∀ (n k r s u c : ℕ) (R : (Fin k → Fin n) → Bool) (ρ : kcs.seed),
    1 ≤ r → r ≤ n →
    (kcs.cost r R s u c ρ : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
        ((s : ℝ) + ((n : ℝ) / r) ^ ((k : ℝ) / 2) *
          ((c : ℝ) + (Nat.sqrt r : ℝ) * (u : ℝ)))

end Qatlib.Concepts.WalkSearch.CollisionSearch
