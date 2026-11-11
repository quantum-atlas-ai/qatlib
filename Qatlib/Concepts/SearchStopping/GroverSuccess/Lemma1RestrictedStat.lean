/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Cosine sum identities away from singular angles

`Lemma1Restricted` states finite cosine-sum identities under nonzero sine-denominator
hypotheses. It includes both the general arithmetic progression and the odd-multiple
specialization needed for randomized Grover success.

For the mathematical background, see [BoyerEtAl1998].

## Main statements

* `Lemma1Restricted`: The conjunction of the arithmetic-progression and odd-multiple cosine-sum
  quotient identities for positive m and nonzero sine denominators.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open scoped BigOperators

/-- The conjunction of the arithmetic-progression and odd-multiple cosine-sum quotient
identities for positive m and nonzero sine denominators. -/
def Lemma1Restricted : Prop :=
  (∀ (α β : ℝ) (m : ℕ), 0 < m → Real.sin β ≠ 0 →
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β) ∧
  (∀ (α : ℝ) (m : ℕ), 0 < m → Real.sin α ≠ 0 →
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α))

end Qatlib.Concepts.SearchStopping.GroverSuccess
