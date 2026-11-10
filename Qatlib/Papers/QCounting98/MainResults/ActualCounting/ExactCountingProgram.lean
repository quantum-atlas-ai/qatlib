/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.ExactCountingCost
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.FoldedEstimate
import Mathlib.Algebra.Order.Floor.Ring
set_option warningAsError false
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

def actualFinalProb {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) (y : Fin (observedFinalGrid z)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle F)
    (standardPaddedAEWord (observedFinalGrid z) (QFTMatrix N) ⟨0,hN⟩)
    (standardInput (observedFinalGrid z) (observedFinalGrid_two hN z) ⟨0,hN⟩))
    (Finset.univ.filter (fun p => p.2 = y))

theorem actualFinalProb_eq {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) (y : Fin (observedFinalGrid z)) :
    actualFinalProb hN F z y =
      (aeLaw (observedFinalGrid z) (QFTMatrix N) ⟨0,hN⟩ (sourceMarked F)
        (qftMatrix_unitary hN) (observedFinalGrid_two hN z)).prob y :=
  standardPaddedAE_label _ _ _ _ (qftMatrix_unitary hN) F y

theorem actualFinalProb_sum {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :
    (∑ y, actualFinalProb hN F z y) = 1 := by
  simp_rw [actualFinalProb_eq]
  exact (aeLaw _ _ _ _ (qftMatrix_unitary hN) (observedFinalGrid_two hN z)).sum_one

theorem actual_exact_joint_mass {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) :
    (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
      actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * (∑ y, actualFinalProb hN F z y)) = 1 := by
  simp_rw [actualFinalProb_sum,mul_one,actualRoughProb_eq]
  exact actual_rough_pair_mass hN F

theorem roundedCount_int_value (N M : ℕ) (y : Fin M) :
    (roundedCount N M y : ℤ) = exactCountOutput N y := by
  unfold roundedCount exactCountOutput
  rw [foldedEstimate_eq]
  apply Int.natCast_floor_eq_floor
  have h : 0 ≤ (N : ℝ)*aeEstimate M y := by unfold aeEstimate; positivity
  linarith

def actualExactSuccessMass {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) : ℝ :=
  ∑ z₁ : Fin (nextCor4RoughGrid N), ∑ z₂ : Fin (nextCor4RoughGrid N),
    actualRoughProb hN F z₁ * actualRoughProb hN F z₂ *
      (∑ y ∈ Finset.univ.filter (fun y : Fin (observedFinalGrid (z₁,z₂)) =>
          roundedCount N (observedFinalGrid (z₁,z₂)) y = (sourceMarked F).card),
        actualFinalProb hN F (z₁,z₂) y)

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

theorem actual_exact_success {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (ht : 1 ≤ ((sourceMarked F).card : ℝ)) (hhalf : ((sourceMarked F).card : ℝ) ≤ (N : ℝ)/2) :
    3/4 ≤ actualExactSuccessMass hN F := by
  rw [actualExactSuccessMass_eq]
  exact nextCor4_success hN (sourceMarked F) ht hhalf (nextCor4_rough_grid_two hN)
    (fun z₁ z₂ => observedFinalGrid_two hN (z₁,z₂))

def actualThreeRunExpectedQueries {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
    (∑ y : Fin (observedFinalGrid z),
      actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * actualFinalProb hN F z y *
        (actualExactBranchQueries hN z : ℝ))

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

theorem actual_adaptive_exact_counter {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (ht : 1 ≤ ((sourceMarked F).card : ℝ)) (hhalf : ((sourceMarked F).card : ℝ) ≤ (N : ℝ)/2) :
    3/4 ≤ actualExactSuccessMass hN F ∧
      actualThreeRunExpectedQueries hN F ≤
        (160*Real.pi+291)*Real.sqrt (((sourceMarked F).card : ℝ)*(N : ℝ)) := by
  refine ⟨actual_exact_success hN F ht hhalf,?_⟩
  rw [actualThreeRunExpectedQueries_eq]
  exact actual_exact_expected_queries_le hN F ht hhalf

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
