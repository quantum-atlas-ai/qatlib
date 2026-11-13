/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv

/-!
# Statement of optimized adversary composition

`Theorem13OptimizedComposition` states a lower bound for the optimized adversary value of a
Boolean composition. It quantifies over nonconstant inner functions on finite types, positive
inner input lengths, and nonnegative coordinate costs, allowing outer costs bounded by the inner
adversary values.

The proposition formalizes the composition principle associated with Theorem 13 of
[HoyerLeeSpalek2007].

## Main statements

* `Theorem13OptimizedComposition`: states the optimized weighted adversary composition
  inequality.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

/-- The proposition that the composed optimized adversary bound dominates the outer bound when
each outer cost is bounded by the corresponding inner bound, under the stated nonconstancy,
input-length, and coordinate-cost assumptions. See [Hoyer, Lee, and Spalek, Theorem
13][HoyerLeeSpalek2007]. -/
def Theorem13OptimizedComposition : Prop :=
  ∀ (k : ℕ) (X : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (n : Fin k → ℕ) (hne : ∀ i, 0 < n i)
    (g : ∀ i, X i → Bool) (hnc : ∀ i, ∃ u v, g i u ≠ g i v)
    (f : (Fin k → Bool) → Bool) (gin : ∀ i, X i → Fin (n i) → Bool)
    (α : (i : Fin k) × Fin (n i) → ℝ) (hα : ∀ c, 0 ≤ α c)
    (β : Fin k → ℝ),
    (∀ i, ENNReal.ofReal (β i) ≤ advPlus (gin i) (g i) (fun q => α ⟨i, q⟩)) →
    advPlus (weightedAdvInput gin) (fun x => f (fun i => g i (x i))) α ≥
      advPlus (fun t => t) f β

end Qatlib.Concepts.AdversaryBounds.AdvDuality
