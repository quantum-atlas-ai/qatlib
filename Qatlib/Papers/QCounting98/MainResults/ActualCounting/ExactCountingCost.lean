/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.StandardProgram
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefinedDefs
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
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Classical BigOperators

def observedFinalGrid {N : ℕ}
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) : ℕ :=
  nextCor4Grid N (firstReadout z.1) (firstReadout z.2)

def actualRoughProb {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) (z : Fin (nextCor4RoughGrid N)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle F)
    (standardPaddedAEWord (nextCor4RoughGrid N) (QFTMatrix N) ⟨0,hN⟩)
    (standardInput (nextCor4RoughGrid N) (nextCor4_rough_grid_two hN) ⟨0,hN⟩))
    (Finset.univ.filter (fun p => p.2 = z))

def actualExactBranchQueries {N : ℕ} (hN : 0 < N)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) : ℕ :=
  2*QueryCount (standardPaddedAEWord (nextCor4RoughGrid N) (QFTMatrix N) ⟨0,hN⟩) +
    QueryCount (standardPaddedAEWord (observedFinalGrid z) (QFTMatrix N) ⟨0,hN⟩)

def actualExactExpectedQueries {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
    actualRoughProb hN F z.1 * actualRoughProb hN F z.2 * (actualExactBranchQueries hN z : ℝ)

theorem actualRoughProb_eq {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (z : Fin (nextCor4RoughGrid N)) : actualRoughProb hN F z = firstProb hN (sourceMarked F) z := by
  unfold actualRoughProb
  rw [standardPaddedAE_label _ _ _ _ (qftMatrix_unitary hN)]
  rfl

theorem observedFinalGrid_two {N : ℕ} (hN : 0 < N)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) : 2 ≤ observedFinalGrid z :=
  nextCor4_grid_two_on_estimates hN z.1 z.2

theorem actualExactBranchQueries_eq {N : ℕ} (hN : 0 < N)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :
    actualExactBranchQueries hN z = 2*nextCor4RoughGrid N + observedFinalGrid z := by
  unfold actualExactBranchQueries
  rw [(standardPaddedAE_resources (nextCor4RoughGrid N) (by have h := nextCor4_rough_grid_two hN; omega) _ _).1,
    (standardPaddedAE_resources (observedFinalGrid z) (by have h := observedFinalGrid_two hN z; omega) _ _).1]

theorem observedFinalGrid_le_ladder {N : ℕ}
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :
    (observedFinalGrid z : ℝ) ≤ 48*ladderCost (pairMin z) N+1 := by
  have hv : 0 ≤ pairMin z := by
    unfold pairMin firstReadout aeEstimate
    positivity
  have hb : Real.sqrt ((pairMin z+1)*((N : ℝ)-pairMin z+1)) ≤ ladderCost (pairMin z) N := by
    unfold ladderCost
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ 48*Real.sqrt ((pairMin z+1)*((N : ℝ)-pairMin z+1)) by positivity)
  change (⌈48*Real.sqrt ((pairMin z+1)*((N : ℝ)-pairMin z+1))⌉₊ : ℝ) ≤ _
  linarith

theorem roughGrid_le (N : ℕ) : (nextCor4RoughGrid N : ℝ) ≤ 80*Real.pi*Real.sqrt (N : ℝ)+1 :=
  (Nat.ceil_lt_add_one (show 0 ≤ 80*Real.pi*Real.sqrt (N : ℝ) by positivity)).le

theorem actual_rough_pair_mass {N : ℕ} (hN : 0 < N) (F : Fin N → Bool) :
    (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ Finset.univ,
      firstProb hN (sourceMarked F) z.1 * firstProb hN (sourceMarked F) z.2) = 1 := by
  rw [Finset.sum_product,← Finset.sum_mul_sum]
  have h : (∑ z, firstProb hN (sourceMarked F) z) = 1 :=
    (aeLaw _ _ _ _ (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).sum_one
  rw [h]
  norm_num

theorem actual_exact_expected_queries_le {N : ℕ} (hN : 0 < N) (F : Fin N → Bool)
    (ht : 1 ≤ ((sourceMarked F).card : ℝ)) (hhalf : ((sourceMarked F).card : ℝ) ≤ (N : ℝ)/2) :
    actualExactExpectedQueries hN F ≤ (160*Real.pi+291)*Real.sqrt (((sourceMarked F).card : ℝ)*(N : ℝ)) := by
  let S := sourceMarked F
  let P : Finset (Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :=
      Finset.univ ×ˢ Finset.univ
  let w := fun z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N) =>
    firstProb hN S z.1 * firstProb hN S z.2
  have hw : ∀ z, 0 ≤ w z := fun z => mul_nonneg
    ((aeLaw _ _ _ S (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).nonneg z.1)
    ((aeLaw _ _ _ S (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).nonneg z.2)
  have hsum : (∑ z ∈ P, w z) = 1 := actual_rough_pair_mass hN F
  have hcost := cor4_expected_cost_le hN S ht hhalf
  change (∑ z ∈ P, w z*ladderCost (pairMin z) N) ≤ 6*Real.sqrt ((S.card : ℝ)*(N : ℝ)) at hcost
  have he : actualExactExpectedQueries hN F ≤
      2*(nextCor4RoughGrid N : ℝ)+48*(∑ z ∈ P, w z*ladderCost (pairMin z) N)+1 := by
    unfold actualExactExpectedQueries
    simp_rw [actualRoughProb_eq,actualExactBranchQueries_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ ∑ z ∈ P, w z*(2*(nextCor4RoughGrid N : ℝ)+48*ladderCost (pairMin z) N+1) := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (hw z)
        linarith [observedFinalGrid_le_ladder z]
      _ = ∑ z ∈ P, ((2*(nextCor4RoughGrid N : ℝ))*w z+48*(w z*ladderCost (pairMin z) N)+w z) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        rw [hsum]
        ring
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hroot : Real.sqrt (N : ℝ) ≤ Real.sqrt ((S.card : ℝ)*(N : ℝ)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hroot1 : 1 ≤ Real.sqrt ((S.card : ℝ)*(N : ℝ)) := Real.one_le_sqrt.mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 80*Real.pi)
  have hrough : (nextCor4RoughGrid N : ℝ) ≤ 80*Real.pi*Real.sqrt ((S.card : ℝ)*(N : ℝ))+1 := by
    linarith [roughGrid_le N]
  nlinarith

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
