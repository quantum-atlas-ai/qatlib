/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchRetry
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchCircuit
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule

/-!
# Uniform output of repeated quantum search

This module proves symmetry of the checked Grover-search output on a nonempty proper marked set.
It propagates this symmetry through each retry stage and sums the exponential schedule to obtain
the uniform final marked-output law, in the search setting of [BoyerEtAl1998].

## Main statements

* `search_checked_output_uniform`: marked indices have equal checked-output mass at a fixed
  iteration count.
* `search_stage_output_uniform`: each marked index receives an equal share of the first-success
  mass at a retry stage.
* `search_final_output_uniform`: summing all stages gives mass 1/|A| on each marked index and
  zero elsewhere.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib.Concepts.SearchStopping.KnownCount

/-- For a nonempty proper marked set, any two marked indices have equal checked-output mass
after the same number of Grover iterations. -/
theorem search_checked_output_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I)
    (j : ℕ) (i k : I) (hi : i ∈ A) (hk : k ∈ A) :
    CheckedOutputMass A j i = CheckedOutputMass A j k := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  obtain ⟨θ,hθ0,hθp,hdensity,h2⟩ := search_principal_angle A hA hproper
  have hs : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩)
  rw [(search_checked_attempt hN A j).2.1 i, (search_checked_attempt hN A j).2.1 k,
    if_pos hi, if_pos hk]
  change BornProb (GroverState A j) i = BornProb (GroverState A j) k
  rw [search_grover_state hN A θ hdensity hs hc j]
  simp only [BornProb, MarkedVector, if_pos hi, if_pos hk]

/-- At each retry stage, the output mass is the first-success mass divided equally among marked
indices, with zero mass on unmarked indices. -/
theorem search_stage_output_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I)
    (sizes : ℕ → ℕ) (s : ℕ) (i : I) :
    RetryOutputMass A sizes s i = if i ∈ A then RetryFirstSuccess A sizes s / A.card else 0 := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hzero (k : I) (hk : k ∉ A) : RetryOutputMass A sizes s k = 0 := by
    unfold RetryOutputMass
    have hz (j : ℕ) : CheckedOutputMass A j k = 0 := by
      rw [(search_checked_attempt hN A j).2.1 k, if_neg hk]
    simp_rw [hz]
    simp
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    have hequal (k : I) (hk : k ∈ A) : RetryOutputMass A sizes s k = RetryOutputMass A sizes s i := by
      unfold RetryOutputMass
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      exact search_checked_output_uniform A hA hproper j k i hk hi
    have hsum : (∑ k, RetryOutputMass A sizes s k) = RetryFirstSuccess A sizes s := by
      unfold RetryOutputMass RetryFirstSuccess CheckedSuccess
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_comm]
    have hsumA : (∑ k, RetryOutputMass A sizes s k) =
        (A.card : ℝ) * RetryOutputMass A sizes s i := by
      calc
        _ = ∑ k ∈ A, RetryOutputMass A sizes s k := by
          symm
          apply Finset.sum_subset (Finset.subset_univ A)
          intro k _ hk
          exact hzero k hk
        _ = ∑ _k ∈ A, RetryOutputMass A sizes s i := Finset.sum_congr rfl (fun k hk => hequal k hk)
        _ = _ := by simp
    have hAr : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
    apply (eq_div_iff hAr).2
    nlinarith [hsum, hsumA]
  · rw [if_neg hi]
    exact hzero i hi

/-- For a nonempty proper marked set, the output masses summed over the exponential retry
schedule yield the uniform distribution on the marked set. -/
theorem search_final_output_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (i : I) :
    HasSum (fun s => RetryOutputMass A (ExponentialSizes (Fintype.card I)) s i)
      (if i ∈ A then 1 / (A.card : ℝ) else 0) := by
  have heach := search_stage_output_uniform A hA hproper (ExponentialSizes (Fintype.card I))
  simp_rw [heach]
  by_cases hi : i ∈ A
  · simp only [if_pos hi]
    exact (search_all_density_termination A hA hproper).div_const _
  · simp only [if_neg hi]
    exact hasSum_zero

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
