/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashVectorData
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Selections of weighted hash deviations

The module bounds a complex sum that selects one component of the hash deviation vector at each
bucket. Coefficients of norm at most one ensure that this selected sum is bounded by
`weightedHashVectorDeviation`.

The estimate is a finite complex norm calculation in the matrix and vector analysis setting of
[Bhatia1997].

## Main statements

* `selected_weighted_hash_moment_bound`: domination of selected weighted deviations by the full
  vector deviation.

## References

* [Bhatia, 1997][Bhatia1997]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- Selecting one component per hash bucket and multiplying by coefficients of norm at most one
gives a sum whose norm is at most the total vector hash deviation. -/
theorem selected_weighted_hash_moment_bound
    (H X A T : Type) [Fintype X] [Fintype A] [DecidableEq A] [Fintype T]
    (hash : H → X → A) (f : T → X → ℂ) (r : H)
    (choose : A → T) (coeff : A → ℂ)
    (hcoeff : ∀ a : A, ‖coeff a‖ ≤ 1) :
    ‖∑ a : A, coeff a * weightedHashDeviation hash (f (choose a)) r a‖ ≤
      weightedHashVectorDeviation hash f r := by
  have hcoordinate (a : A) :
      ‖weightedHashDeviation hash (f (choose a)) r a‖ ≤
        Real.sqrt (∑ k : T, Complex.normSq
          (weightedHashDeviation hash (f k) r a)) := by
    apply Real.le_sqrt_of_sq_le
    rw [Complex.sq_norm]
    exact Finset.single_le_sum
      (f := fun k : T => Complex.normSq (weightedHashDeviation hash (f k) r a))
      (fun k _ => Complex.normSq_nonneg (weightedHashDeviation hash (f k) r a))
      (Finset.mem_univ (choose a))
  calc
    _ ≤ ∑ a : A, ‖coeff a * weightedHashDeviation hash (f (choose a)) r a‖ :=
      norm_sum_le _ _
    _ = ∑ a : A, ‖coeff a‖ *
        ‖weightedHashDeviation hash (f (choose a)) r a‖ := by
      simp_rw [norm_mul]
    _ ≤ ∑ a : A, ‖weightedHashDeviation hash (f (choose a)) r a‖ := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hcoeff a)
          (norm_nonneg (weightedHashDeviation hash (f (choose a)) r a))
    _ ≤ weightedHashVectorDeviation hash f r := by
      exact Finset.sum_le_sum (fun a _ => hcoordinate a)

end Qatlib.Concepts.ProbabilityCore.Concentration
