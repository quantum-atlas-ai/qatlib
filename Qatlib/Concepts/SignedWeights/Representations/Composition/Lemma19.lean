/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.GeneralAdversary

/-!
# Weighted Composition Upper Bound

This module presents the weighted nonnegative adversary composition upper bound associated with
Lemma 19 of [HoyerLeeSpalek2007]. The coordinate costs `α` are strictly positive, the outer and
every inner function are nonconstant, and the effective inner costs `blockCosts` are finite.
Under these hypotheses, `advAlphaENN` for the composed input is bounded by the outer weighted
value with those effective costs.

## Main statements

- `lemma19_upper_bound` transfers the composition upper bound to the source-facing statement.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Lemma 19.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Composition

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod

noncomputable section

/-- For strictly positive coordinate costs, nonconstant outer and inner functions, and finite
effective block costs, the weighted nonnegative adversary value of the composition is at
most the outer value with those block costs. This is Lemma 19 of [HoyerLeeSpalek2007]. -/
theorem lemma19_upper_bound
    {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (α : ((i : Fin k) × Fin (n i)) → ℝ)
    (hα : ∀ c, 0 < α c) (hfn : ∃ u v : Fin k → Bool, f u ≠ f v)
    (hgn : ∀ i, ∃ a b : Y i, g i a ≠ g i b)
    (hfin : ∀ i, blockCosts gin g α i < ⊤) :
    advAlphaENN (composedInput gin) (composedFunction g f)
      (fun c => ENNReal.ofReal (α c)) ≤
      advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g α) :=
  composition_upper_bound_on_source_scope gin g f α hα hfn hgn hfin

end

end Qatlib.Concepts.SignedWeights.Representations.Composition
