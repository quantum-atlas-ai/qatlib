/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma1RestrictedStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.FiniteTrigonometricSums

/-!
# Proofs of restricted cosine sum identities

`lemma1_cosine_sum_mul` and `lemma1_odd_cosine_sum_mul` provide denominator-free finite cosine
identities. Their quotient forms require nonzero sine denominators and together establish
`lemma1Restricted`.

For the mathematical background, see [BoyerEtAl1998].

## Main statements

* `lemma1Restricted`: Establishes the two non-singular finite cosine-sum identities packaged by
  `Lemma1Restricted`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open scoped BigOperators

/-- Multiplying the arithmetic-progression cosine sum by sin(β) gives sin(mβ) cos(α + (m − 1)β). -/
theorem lemma1_cosine_sum_mul (α β : ℝ) (m : ℕ) :
    Real.sin β * (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) :=
  cosine_arithmetic_sum_mul α β m

/-- For sin(β) ≠ 0, evaluates the arithmetic-progression cosine sum by its sine-cosine quotient. -/
theorem lemma1_cosine_sum (α β : ℝ) (m : ℕ) (hβ : Real.sin β ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β :=
  cosine_arithmetic_sum α β m hβ

/-- Multiplying the odd-multiple cosine sum by 2 sin(α) gives sin(2mα). -/
theorem lemma1_odd_cosine_sum_mul (α : ℝ) (m : ℕ) :
    (2 * Real.sin α) * (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) :=
  cosine_odd_sum_mul α m

/-- For sin(α) ≠ 0, the odd-multiple cosine sum is sin(2mα)/(2 sin(α)). -/
theorem lemma1_odd_cosine_sum (α : ℝ) (m : ℕ) (hα : Real.sin α ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α) :=
  cosine_odd_sum α m hα

/-- Establishes the two non-singular finite cosine-sum identities packaged by
`Lemma1Restricted`. See [BoyerEtAl1998]. -/
theorem lemma1Restricted : Lemma1Restricted :=
  ⟨fun α β m _ hβ => lemma1_cosine_sum α β m hβ,
    fun α m _ hα => lemma1_odd_cosine_sum α m hα⟩

end Qatlib.Concepts.SearchStopping.GroverSuccess
