/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Cosine sum identities including singular angles

`Lemma1Corrected` states finite cosine-sum formulas with explicit branches when the sine
denominator vanishes. It covers arithmetic progressions of angles and their odd-multiple
specialization, which are used in randomized Grover success calculations.

For the mathematical background, see [BoyerEtAl1998].

## Main statements

* `Lemma1Corrected`: The conjunction of the arithmetic-progression and odd-multiple cosine-sum
  identities for positive m, with separate branches for vanishing sine denominators.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.GroverSuccess
open scoped BigOperators

/-- The conjunction of the arithmetic-progression and odd-multiple cosine-sum identities for
positive m, with separate branches for vanishing sine denominators. -/
def Lemma1Corrected : Prop :=
  (∀ (α β : ℝ) (m : ℕ), 0 < m →
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      if Real.sin β = 0 then (m : ℝ) * Real.cos α
      else Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β) ∧
  (∀ (α : ℝ) (m : ℕ), 0 < m →
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      if Real.sin α = 0 then (m : ℝ) * Real.cos α
      else Real.sin (2 * m * α) / (2 * Real.sin α))

end Qatlib.Concepts.SearchStopping.GroverSuccess
