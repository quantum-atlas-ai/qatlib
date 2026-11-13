/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv

/-!
# Statement of adversary weak duality

`Theorem18WeakDuality` states that the optimized nonnegative adversary value is bounded above by
`minimaxAlpha` for finite input and coordinate types and strictly positive coordinate costs.

This records the weak-duality direction associated with the adversary minimax characterization
in Theorem 18 of [HoyerLeeSpalek2007].

## Main statements

* `Theorem18WeakDuality`: states `advNonneg input g α ≤ minimaxAlpha input g α` for positive
  costs.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

/-- The proposition that `advNonneg input g α ≤ minimaxAlpha input g α` for finite input and
coordinate types and strictly positive costs. This is the weak-duality direction associated
with [Hoyer, Lee, and Spalek, Theorem 18][HoyerLeeSpalek2007]. -/
def Theorem18WeakDuality : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (κ : Type) [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (hα : ∀ i, 0 < α i),
    advNonneg input g α ≤ minimaxAlpha input g α

end Qatlib.Concepts.AdversaryBounds.AdvDuality
