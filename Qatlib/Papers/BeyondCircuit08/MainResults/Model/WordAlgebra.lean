/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

/-!
# Products and crossing counts of braid words

The evaluation `evalWord` takes concatenation of signed braid words to multiplication and sends
the empty word to the identity. Crossing counts are additive under concatenation and equal one
for a singleton word, providing elementary word bookkeeping for the synthesis arguments in
[Jordan2008].

## Main statements

* `evalWord_append`: evaluates concatenation as a product.
* `crossingCount_append`: crossing counts add under concatenation.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

open scoped Matrix BigOperators

/-- Evaluating the concatenation of two braid words gives the product of their evaluations in
any monoid equipped with an inverse operation [Jordan2008]. -/
theorem evalWord_append {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) (w₁ w₂ : BraidWord n) :
    evalWord gen (List.append w₁ w₂) = evalWord gen w₁ * evalWord gen w₂ := by
  simp [evalWord, List.map_append, List.prod_append]

/-- The empty braid word evaluates to the identity. -/
theorem evalWord_nil {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) : evalWord gen [] = 1 := rfl

/-- The crossing count of a concatenation is the sum of the crossing counts of its two words
[Jordan2008]. -/
theorem crossingCount_append {n : ℕ} (w₁ w₂ : BraidWord n) :
    crossingCount (List.append w₁ w₂) = crossingCount w₁ + crossingCount w₂ := by
  simp [crossingCount]

/-- A braid word containing one signed generator has crossing count one. -/
theorem crossingCount_singleton {n : ℕ} (g : Fin (n - 1) × Bool) :
    crossingCount [g] = 1 := rfl

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
