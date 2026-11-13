/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-!
# Universal matching scores and positive effects

This module records the universal matching score formula from [SasakiCarlini2002] as `qmScore`.
It also proves positivity of two sums of conjugate outer products and retains the assumed
completeness identity.

The theorem `universal_matching_POVM` supplies the positive complete pair from given vector
families; the completeness of those families is an explicit hypothesis.

## Main statements

* `qmScore_eq`: the explicit binomial formula for the score.
* `universal_matching_POVM`: positivity of the two effects under the supplied completeness
  hypothesis.

## References

* [Sasaki and Carlini, 2002][SasakiCarlini2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.UniversalMatching

/-- The universal matching score given by one half plus the weighted endpoint and interior
binomial square-root terms. -/
def qmScore (N : ℕ) : ℝ :=
  1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
    (2 * Real.sqrt (N : ℝ) +
      ∑ k ∈ Finset.Icc 1 (N - 1),
        Real.sqrt (Nat.choose N k : ℝ) *
          Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)))

/-- The quantity `qmScore N` equals its explicit binomial square-root formula. -/
theorem qmScore_eq (N : ℕ) :
    qmScore N =
      1 / 2 + (Real.sqrt 2 / (2 : ℝ) ^ (N + 4)) *
        (2 * Real.sqrt (N : ℝ) +
          ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k : ℝ) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) :=
  rfl

/-- If the two sums of conjugate outer products add to the identity, then both sums are positive
semidefinite and form a complete pair. -/
theorem universal_matching_POVM (N : ℕ)
    (kPlus kMinus : Fin (N + 1) → (Fin (N + 1) → ℂ))
    (hcomplete :
      (∑ k, vecMulVec (kPlus k) (star (kPlus k)))
        + (∑ k, vecMulVec (kMinus k) (star (kMinus k))) = 1) :
    (∑ k, vecMulVec (kPlus k) (star (kPlus k))).PosSemidef
      ∧ (∑ k, vecMulVec (kMinus k) (star (kMinus k))).PosSemidef
      ∧ (∑ k, vecMulVec (kPlus k) (star (kPlus k)))
          + (∑ k, vecMulVec (kMinus k) (star (kMinus k))) = 1 := by
  refine ⟨?_, ?_, hcomplete⟩
  · exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨N + 1, kPlus, rfl⟩
  · exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨N + 1, kMinus, rfl⟩

end Qatlib.Papers.QMatching02.MainResults.UniversalMatching
