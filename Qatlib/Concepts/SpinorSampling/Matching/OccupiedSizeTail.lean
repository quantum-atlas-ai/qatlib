/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.OccupiedAddressMoments

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Occupied Size Tail

Occupied Size Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for occupied Quarter Bad Mass in the occupied size tail model. -/
def occupiedQuarterBadMass (n : ℕ) : ℝ :=
  (cohortLaw (uniformLaw S) n).expect
    (fun J => if occupiedCount J < (n : ℝ)/4 then 1 else 0)

/-- Complete original `occupied_quarter_lower_tail` guarantee for `OccupiedSizeTail`; all source hypotheses and output obligations are retained. -/
theorem occupied_quarter_lower_tail (n : ℕ) (hn0 : 0 < n) (hn : n ≤ Fintype.card S) :
    occupiedQuarterBadMass (S:=S) n ≤ Real.exp (-(n : ℝ)/8) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsum : (∑ _i : Fin n, (1 : ℝ)^2) = (n : ℝ) := by simp
  have hmean :
      (independentSampleLaw (fun _i : Fin n => uniformLaw S)).expect
        (fun J => -occupiedCount J) = -expectedOccupied (S:=S) n := by
    simp only [FinDist.expect, independentSampleLaw, expectedOccupied,
      cohortLaw, FinDist.probOf, mul_neg, ← Finset.sum_neg_distrib]
  have htail := (finite_product_bounded_differences_tail S n
    (fun _ => uniformLaw S) (fun J => -occupiedCount J) (fun _ => 1) ((n : ℝ)/4)
    (fun _ => by norm_num) (by rw [hsum]; exact hnR) (by positivity)
    (by
      intro i J K hJK
      simpa only [neg_sub_neg, abs_sub_comm] using occupied_count_coordinate J K i hJK)).1
  rw [hmean, hsum] at htail
  have he : -2*((n : ℝ)/4)^2/(n : ℝ) = -(n : ℝ)/8 := by
    field_simp [ne_of_gt hnR]
    ring
  rw [he] at htail
  have hhalf := expected_occupied_half (S:=S) n hn
  calc
    _ ≤ (cohortLaw (uniformLaw S) n).expect
        (fun J => if -expectedOccupied (S:=S) n+(n : ℝ)/4 ≤ -occupiedCount J
          then 1 else 0) := by
      apply finite_expect_mono
      intro J
      by_cases hj : occupiedCount J < (n : ℝ)/4
      · have hu : -expectedOccupied (S:=S) n+(n : ℝ)/4 ≤ -occupiedCount J := by linarith
        simp only [ite_eq_left hj, ite_eq_left hu, le_refl]
      · simp only [ite_eq_right hj]
        split_ifs <;> norm_num
    _ ≤ _ := by
      change (∑ J : Fin n → S, (cohortLaw (uniformLaw S) n).prob J *
        (if -expectedOccupied (S:=S) n+(n : ℝ)/4 ≤ -occupiedCount J then 1 else 0)) ≤ _
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      exact htail

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_quarter_lower_tail
