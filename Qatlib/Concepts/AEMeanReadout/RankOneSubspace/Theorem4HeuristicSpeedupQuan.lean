/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Corollary1ExpectedSearchQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem4HeuristicSpeedupStat

/-!
# Average search cost for a finite heuristic model

`theorem4HeuristicSpeedup` proves the finite-distribution heuristic search specification. Each
instance has a nonempty marked set of size at most half the search space, and the conclusion
bounds the average expected phase-query count. For background, see
[BrassardHoyerTapp1998Counting].

## Main statements

* `theorem4HeuristicSpeedup`: For a finite distribution of nonempty marked sets occupying at
  most half a positive search space, sound geometric search schedules achieve every positive
  failure tolerance with average expected phase-query count at most `50 * sqrt 2` times the
  square root of the average inverse marked fraction. See [BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal

/-- For a finite distribution of nonempty marked sets occupying at most half a positive search
space, sound geometric search schedules achieve every positive failure tolerance with
average expected phase-query count at most `50 * sqrt 2` times the square root of the
average inverse marked fraction. See [BrassardHoyerTapp1998Counting]. -/
theorem theorem4HeuristicSpeedup : Theorem4HeuristicSpeedup := by
  intro ℱ _ _ P n good marked hn hpos hsparse ε hε
  choose Mof Tof hfail hcost hsup using
    fun F' => corollary1ExpectedSearch n (marked F') hn (hpos F') (hsparse F') ε hε
  refine ⟨Mof, Tof, hfail, ?_, hsup⟩
  have hc₁ : ∀ F' ∈ (Finset.univ : Finset ℱ),
      ENNReal.ofReal (P.prob F') *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix n)
            (qftMatrix_unitary hn) ⟨0, hn⟩ (marked F')
            (fun y => decide (y ∈ marked F'))
            (geometricSearchSchedule (Mof F') (Tof F')))
          (fun tr => (tr.phaseQueries : ℝ≥0∞)) ≤
        ENNReal.ofReal (P.prob F' *
          (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))) := by
    intro F' _
    rw [ENNReal.ofReal_mul (P.nonneg F')]
    exact mul_le_mul le_rfl (hcost F') (zero_le : (0:ℝ≥0∞) ≤ _) (zero_le : (0:ℝ≥0∞) ≤ _)
  have hc₂ : ∑ F' : ℱ, ENNReal.ofReal (P.prob F' *
        (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))) =
      ENNReal.ofReal (∑ F' : ℱ, P.prob F' *
        (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))) :=
    (ENNReal.ofReal_sum_of_nonneg
      fun F' _ => mul_nonneg (P.nonneg F') (by positivity)).symm
  have hsumconst : ∑ F' : ℱ, P.prob F' *
        (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ))) =
      50 * Real.sqrt 2 * ∑ F' : ℱ, P.prob F' *
        Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun F' _ => by ring
  have hnn1 : 0 ≤ ∑ F' : ℱ, P.prob F' * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)) :=
    Finset.sum_nonneg fun F' _ => mul_nonneg (P.nonneg F') (Real.sqrt_nonneg _)
  have hnnT : 0 ≤ ∑ F' : ℱ, P.prob F' * ((n : ℝ) / ((marked F').card : ℝ)) :=
    Finset.sum_nonneg fun F' _ => mul_nonneg (P.nonneg F') (by positivity)
  have hcs : (∑ F' : ℱ, P.prob F' * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ))) ^ 2 ≤
      ∑ F' : ℱ, P.prob F' * ((n : ℝ) / ((marked F').card : ℝ)) := by
    refine le_trans (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun F' => P.prob F' * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))
      (f := fun F' => P.prob F')
      (g := fun F' => P.prob F' * ((n : ℝ) / ((marked F').card : ℝ)))
      (fun F' _ => P.nonneg F')
      (fun F' _ => mul_nonneg (P.nonneg F') (by positivity))
      (fun F' _ => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring))) ?_
    rw [P.sum_one, one_mul]
  have hsqrt : ∑ F' : ℱ, P.prob F' * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)) ≤
      Real.sqrt (∑ F' : ℱ, P.prob F' * ((n : ℝ) / ((marked F').card : ℝ))) :=
    (Real.le_sqrt hnn1 hnnT).mpr hcs
  calc ∑ F' : ℱ, ENNReal.ofReal (P.prob F') *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix n)
            (qftMatrix_unitary hn) ⟨0, hn⟩ (marked F')
            (fun y => decide (y ∈ marked F'))
            (geometricSearchSchedule (Mof F') (Tof F')))
          (fun tr => (tr.phaseQueries : ℝ≥0∞)) ≤
      ∑ F' : ℱ, ENNReal.ofReal (P.prob F' *
        (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))) :=
        Finset.sum_le_sum hc₁
    _ = ENNReal.ofReal (∑ F' : ℱ, P.prob F' *
        (50 * Real.sqrt 2 * Real.sqrt ((n : ℝ) / ((marked F').card : ℝ)))) := hc₂
    _ = ENNReal.ofReal (50 * Real.sqrt 2 * ∑ F' : ℱ, P.prob F' *
        Real.sqrt ((n : ℝ) / ((marked F').card : ℝ))) := by rw [hsumconst]
    _ ≤ ENNReal.ofReal (50 * Real.sqrt 2 *
        Real.sqrt (∑ F' : ℱ, P.prob F' * ((n : ℝ) / ((marked F').card : ℝ)))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsqrt (by positivity))

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
