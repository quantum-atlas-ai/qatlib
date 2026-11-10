/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.StructureCore

open Matrix
set_option warningAsError false

def extractionSameSign : QState (Fin 8 × Unit) :=
  fun r => if 6 ≤ r.1.val then 1 else 0

def extractionOppositeSign : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 6 then 1 else if r.1.val = 7 then -1 else 0

def zeroSignalTaylorSolution : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 0 then 1 else if 6 ≤ r.1.val then -1 else 0

theorem zeroSignalTaylorSolution_solves :
    taylorStepMatrix 1 5 1 (0 : Matrix Unit Unit ℂ) *ᵥ zeroSignalTaylorSolution =
      taylorRHS 1 5 1 1 (fun _ : Unit => 1) 0 := by
  ext ⟨r, n⟩
  cases n
  fin_cases r <;>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Fintype.sum_unique] <;>
    norm_num [taylorStepMatrix, taylorRHS, zeroSignalTaylorSolution, Fin.ext_iff]

theorem zeroSignalTaylor_jump_entry :
    taylorStepMatrix 1 5 1 (0 : Matrix Unit Unit ℂ) (6, ()) (0, ()) = 1 := by
  norm_num [taylorStepMatrix, Fin.ext_iff]

theorem taylorODESolution_zero_signal (t : ℝ) :
    taylorODESolution (0 : Matrix Unit Unit ℂ) 0 (fun _ => 1) t = (fun _ => 1) := by
  have h := orderedForcedSolution_unique (fun _ => (0 : Matrix Unit Unit ℂ))
    (fun _ => (0 : QState Unit)) continuous_const continuous_const 0 (fun _ => 1)
    (fun _ => (fun _ : Unit => (1 : ℂ))) rfl (fun t => by
      simpa using! (hasDerivAt_const t (fun _ : Unit => (1 : ℂ))))
  simpa [taylorODESolution] using! (congrFun h t).symm

theorem zeroSignalTaylorSolution_extract :
    taylorExtract 1 5 1 zeroSignalTaylorSolution = (fun _ : Unit => -2) := by
  ext n
  norm_num [taylorExtract, zeroSignalTaylorSolution, Fin.sum_univ_succ]

theorem zeroSignalTaylorSolution_final :
    taylorBlock zeroSignalTaylorSolution (taylorTimeLabel 1 5 1 1 (by omega)) =
      (fun _ : Unit => -1) := by
  ext n
  norm_num [taylorBlock, taylorTimeLabel, zeroSignalTaylorSolution]

theorem extractionSameSign_extract :
    taylorExtract 1 5 1 extractionSameSign = (fun _ : Unit => 2) := by
  ext n
  norm_num [taylorExtract, extractionSameSign, Fin.sum_univ_succ]

theorem extractionSameSign_mass :
    MeasureProb extractionSameSign (taylorSuccessSet 1 5 1) = 2 := by
  norm_num [MeasureProb, BornProb, taylorSuccessSet, extractionSameSign,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem extractionSameSign_extract_norm_sq :
    ‖stateVector (taylorExtract 1 5 1 extractionSameSign)‖ ^ 2 = 4 := by
  rw [extractionSameSign_extract, stateVector_norm_sq]
  norm_num [MeasureProb, BornProb]

theorem extraction_mass_identity_counterexample :
    ‖stateVector (taylorExtract 1 5 1 extractionSameSign)‖ ^ 2 ≠
      MeasureProb extractionSameSign (taylorSuccessSet 1 5 1) := by
  rw [extractionSameSign_extract_norm_sq, extractionSameSign_mass]
  norm_num

theorem extractionOppositeSign_extract :
    taylorExtract 1 5 1 extractionOppositeSign = 0 := by
  ext n
  norm_num [taylorExtract, extractionOppositeSign, Fin.sum_univ_succ]

theorem extractionOppositeSign_mass :
    MeasureProb extractionOppositeSign (taylorSuccessSet 1 5 1) = 2 := by
  norm_num [MeasureProb, BornProb, taylorSuccessSet, extractionOppositeSign,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

end Qatlib.Papers.QLinearODE17.StructureCore
