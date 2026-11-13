/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.ExactCountingCost
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.FoldedEstimate
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Success and cost of the adaptive exact-counting program

This module defines the joint probabilities for two rough standard counting runs followed by a
final run at `observedFinalGrid`. The output uses `roundedCount`, which is identified with the
integer-valued analytical output in the exact-counting analysis of
[BrassardHoyerTapp1998Counting].

The joint law has total mass one. For marked count `1 ≤ t ≤ N / 2`,
`actual_adaptive_exact_counter` combines success probability at least `3 / 4` with an expected
query count at most `(160 * π + 291) * sqrt (t * N)`.

## Main statements

* `actual_exact_joint_mass`: normalization of the three-run joint law.
* `actual_exact_success`: success probability at least three quarters.
* `actualThreeRunExpectedQueries_eq`: agreement of the joint-law and branch-law cost
  expressions.
* `actual_adaptive_exact_counter`: the combined exact-counting success and expected-cost bounds.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17 (exactCountOutput)
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Classical BigOperators

/-- The probability of final label `y` in the standard counting circuit at the precision chosen
from the rough observation pair `z`. -/
def actualFinalProb {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) (y : Fin (observedFinalGrid z)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle F)
    (standardPaddedAEWord (observedFinalGrid z) (QFTMatrix N) ⟨0,hN⟩)
    (standardInput (observedFinalGrid z) (observedFinalGrid_two hN z) ⟨0,hN⟩))
    (Finset.univ.filter (fun p => p.2 = y))

/-- The final standard-circuit label probability equals the corresponding value of `aeLaw` at
`observedFinalGrid z`. -/
theorem actualFinalProb_eq {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) (y : Fin (observedFinalGrid z)) :
    actualFinalProb hN F z y =
      (aeLaw (observedFinalGrid z) (QFTMatrix N) ⟨0,hN⟩ (sourceMarked F)
        (qftMatrix_unitary hN) (observedFinalGrid_two hN z)).prob y :=
  standardPaddedAE_label _ _ _ _ (qftMatrix_unitary hN) F y

/-- For each pair of rough observations, the final-label probabilities sum to one. -/
theorem actualFinalProb_sum {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :
    (∑ y, actualFinalProb hN F z y) = 1 := by
  simp_rw [actualFinalProb_eq]
  exact (aeLaw _ _ _ _ (qftMatrix_unitary hN) (observedFinalGrid_two hN z)).sum_one

/-- The joint mass of two independent rough counting outcomes and the observation-dependent
final counting outcome equals one. -/
theorem actual_exact_joint_mass {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) :
    (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
      actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * (∑ y, actualFinalProb hN F z y)) = 1 := by
  simp_rw [actualFinalProb_sum,mul_one,actualRoughProb_eq]
  exact actual_rough_pair_mass hN F

/-- The integer coercion of `roundedCount N M y` equals the analytical exact-count output
`exactCountOutput N y`. -/
theorem roundedCount_int_value (N M : ℕ) (y : Fin M) :
    (roundedCount N M y : ℤ) = exactCountOutput N y := by
  unfold roundedCount exactCountOutput
  rw [foldedEstimate_eq]
  apply Int.natCast_floor_eq_floor
  have h : 0 ≤ (N : ℝ)*aeEstimate M y := by unfold aeEstimate; positivity
  linarith

/-- The joint probability that the rounded final estimate equals the marked count, summed over
both rough labels and all successful final labels. -/
def actualExactSuccessMass {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) : ℝ :=
  ∑ z₁ : Fin (nextCor4RoughGrid N), ∑ z₂ : Fin (nextCor4RoughGrid N),
    actualRoughProb hN F z₁ * actualRoughProb hN F z₂ *
      (∑ y ∈ Finset.univ.filter (fun y : Fin (observedFinalGrid (z₁,z₂)) =>
          roundedCount N (observedFinalGrid (z₁,z₂)) y = (sourceMarked F).card),
        actualFinalProb hN F (z₁,z₂) y)

/-- The standard-circuit exact-count success mass equals the analytical quantity
`nextCor4SuccessMass` for `sourceMarked F`. -/
theorem actualExactSuccessMass_eq {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) :
    actualExactSuccessMass hN F =
      nextCor4SuccessMass hN (sourceMarked F) (nextCor4_rough_grid_two hN)
        (fun z₁ z₂ => observedFinalGrid_two hN (z₁,z₂)) := by
  have hd (M : ℕ) (y : Fin M) :
      roundedCount N M y = (sourceMarked F).card ↔ exactCountOutput N y = ((sourceMarked F).card : ℤ) := by
    rw [← roundedCount_int_value]
    exact Int.natCast_inj.symm
  unfold actualExactSuccessMass nextCor4SuccessMass nextCor4FinalMass
  simp_rw [actualRoughProb_eq,actualFinalProb_eq,hd]
  rfl

/-- For marked count `1 ≤ t ≤ N / 2`, the adaptive three-run counter returns the exact count
with probability at least `3 / 4`. See the exact-counting construction in
[BrassardHoyerTapp1998Counting]. -/
theorem actual_exact_success {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (ht : 1 ≤ ((sourceMarked F).card : ℝ)) (hhalf : ((sourceMarked F).card : ℝ) ≤ (N : ℝ)/2) :
    3/4 ≤ actualExactSuccessMass hN F := by
  rw [actualExactSuccessMass_eq]
  exact nextCor4_success hN (sourceMarked F) ht hhalf (nextCor4_rough_grid_two hN)
    (fun z₁ z₂ => observedFinalGrid_two hN (z₁,z₂))

/-- The expected branch query count under the full joint law of both rough labels and the final
label. -/
def actualThreeRunExpectedQueries {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
    (∑ y : Fin (observedFinalGrid z),
      actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * actualFinalProb hN F z y *
        (actualExactBranchQueries hN z : ℝ))

/-- Summing the query cost over the final label leaves the expected cost
`actualExactExpectedQueries` unchanged. -/
theorem actualThreeRunExpectedQueries_eq {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) :
    actualThreeRunExpectedQueries hN F = actualExactExpectedQueries hN F := by
  unfold actualThreeRunExpectedQueries actualExactExpectedQueries
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = ∑ y : Fin (observedFinalGrid z),
        (actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * (actualExactBranchQueries hN z : ℝ)) *
          actualFinalProb hN F z y := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [← Finset.mul_sum,actualFinalProb_sum,mul_one]

/-- For marked count `1 ≤ t ≤ N / 2`, the adaptive counter has success probability at least `3 /
4` and expected query count at most `(160 * π + 291) * sqrt (t * N)`. This gives explicit
success and cost bounds for [Brassard et al., Corollary 4][BrassardHoyerTapp1998Counting]. -/
theorem actual_adaptive_exact_counter {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (ht : 1 ≤ ((sourceMarked F).card : ℝ)) (hhalf : ((sourceMarked F).card : ℝ) ≤ (N : ℝ)/2) :
    3/4 ≤ actualExactSuccessMass hN F ∧
      actualThreeRunExpectedQueries hN F ≤
        (160*Real.pi+291)*Real.sqrt (((sourceMarked F).card : ℝ)*(N : ℝ)) := by
  refine ⟨actual_exact_success hN F ht hhalf,?_⟩
  rw [actualThreeRunExpectedQueries_eq]
  exact actual_exact_expected_queries_le hN F ht hhalf

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
