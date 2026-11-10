/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.StandardProgram
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.FoldedEstimate
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem6AmplitudeEstimationQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open scoped Classical BigOperators

theorem standard_theorem5_folded (N P : ℕ) (F : Fin N → Bool) (hN : 0 < N)
    (ht : (levelSet F).card ≤ N/2) (hP : 4 ≤ P) :
    QueryCount (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩) = P ∧
      8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N : ℝ)*foldedEstimate P z-((levelSet F).card : ℝ)| <
          2*Real.pi/(P : ℝ)*Real.sqrt (((levelSet F).card : ℝ)*(N : ℝ)) +
            Real.pi^2/(P : ℝ)^2*(N : ℝ)),
        MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩)
          (standardInput P (by omega) ⟨0,hN⟩)) (Finset.univ.filter (fun p => p.2 = z)) := by
  simp_rw [foldedEstimate_eq]
  exact standard_theorem5 N P F hN ht hP

theorem standard_corollary2 (N P : ℕ) (F : Fin N → Bool) (c : ℝ)
    (hN : 0 < N) (ht : (levelSet F).card ≤ N/2) (hc : 0 < c)
    (hPc : (P : ℝ) = c*Real.sqrt (N : ℝ)) (hP : 4 ≤ P) :
    QueryCount (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩) = P ∧
      8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N : ℝ)*foldedEstimate P z-((levelSet F).card : ℝ)| <
          2*Real.pi/c*Real.sqrt ((levelSet F).card : ℝ)+Real.pi^2/c^2),
        MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩)
          (standardInput P (by omega) ⟨0,hN⟩)) (Finset.univ.filter (fun p => p.2 = z)) := by
  refine ⟨(standardPaddedAE_resources P (by omega) (QFTMatrix N) ⟨0,hN⟩).1,?_⟩
  simp_rw [foldedEstimate_eq,standardPaddedAE_label P (by omega) (QFTMatrix N) ⟨0,hN⟩
    (qftMatrix_unitary hN)]
  exact (source_corollary2_fixed_budget N P F c hN ht hc hPc hP).2

theorem standard_theorem6 {I : Type} [Fintype I] [DecidableEq I]
    (P : ℕ) (A : Matrix I I ℂ) (j : I) (F : I → Bool)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hP : 4 ≤ P) :
    QueryCount (standardPaddedAEWord P A j) = P ∧
      8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |foldedEstimate P z-MeasureProb (preparedAAState A j) (sourceMarked F)| <
          2*Real.pi/(P : ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) (sourceMarked F))+
            Real.pi^2/(P : ℝ)^2),
        MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P A j)
          (standardInput P (by omega) j)) (Finset.univ.filter (fun p => p.2 = z)) := by
  refine ⟨(standardPaddedAE_resources P (by omega) A j).1,?_⟩
  simp_rw [foldedEstimate_eq,standardPaddedAE_label P (by omega) A j hA]
  exact theorem6AmplitudeEstimation I P A j (sourceMarked F) hA hP

theorem standard_half_window (N P : ℕ) (F : Fin N → Bool) (hN : 0 < N)
    (ht : (levelSet F).card ≤ N/2) (hP : 4 ≤ P) (htpos : 0 < (levelSet F).card)
    (hbig : Real.pi*(2+Real.sqrt 6)*
      Real.sqrt (((levelSet F).card : ℝ)*(N : ℝ)) < (P : ℝ)) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N : ℝ)*aeEstimate P z-((levelSet F).card : ℝ)| < 1/2),
      MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩)
        (standardInput P (by omega) ⟨0,hN⟩)) (Finset.univ.filter (fun p => p.2 = z)) := by
  simp_rw [standardPaddedAE_label P (by omega) (QFTMatrix N) ⟨0,hN⟩ (qftMatrix_unitary hN)]
  exact source_theorem5_half_window N P F hN ht hP htpos hbig

theorem standard_rounded_count_success (N P : ℕ) (F : Fin N → Bool) (hN : 0 < N)
    (ht : (levelSet F).card ≤ N/2) (hP : 4 ≤ P) (htpos : 0 < (levelSet F).card)
    (hbig : Real.pi*(2+Real.sqrt 6)*
      Real.sqrt (((levelSet F).card : ℝ)*(N : ℝ)) < (P : ℝ)) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P => roundedCount N P z = (levelSet F).card),
      MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (QFTMatrix N) ⟨0,hN⟩)
        (standardInput P (by omega) ⟨0,hN⟩)) (Finset.univ.filter (fun p => p.2 = z)) := by
  refine (standard_half_window N P F hN ht hP htpos hbig).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact roundedCount_exact N P (levelSet F).card z hz
  · intro z _ _
    exact measureProb_nonneg _ _

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
