/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux

/-!
# Examples separating coherent extraction from measurement

This module gives explicit scalar Taylor states that distinguish coherent extraction from
measurement of the success labels. Same-sign final blocks have extraction squared norm 4 but
success mass 2; opposite-sign final blocks have zero extraction and success mass 2.

A zero-generator solution also records the positive jump coupling of `taylorStepMatrix` and the
resulting negative final block. These examples clarify the sign and readout conventions needed
for the ODE construction in [BerryEtAl2017ODE].

## Main statements

* `zeroSignalTaylorSolution_solves`: An explicit solution for the original Taylor jump
  convention.
* `extraction_mass_identity_counterexample`: Coherent extraction squared norm can differ from
  success-set mass.
* `extractionOppositeSign_extract`: Opposite signs cancel under coherent extraction.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.StructureCore

open Matrix
set_option warningAsError false

/-- The state on eight scalar labels with amplitude 1 at labels six and seven and zero
elsewhere. -/
def extractionSameSign : QState (Fin 8 × Unit) :=
  fun r => if 6 ≤ r.1.val then 1 else 0

/-- The state on eight scalar labels with amplitude 1 at label six, -1 at label seven, and zero
elsewhere. -/
def extractionOppositeSign : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 6 then 1 else if r.1.val = 7 then -1 else 0

/-- The state on eight scalar labels with amplitude 1 at label zero, -1 at labels six and seven,
and zero elsewhere. -/
def zeroSignalTaylorSolution : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 0 then 1 else if 6 ≤ r.1.val then -1 else 0

/-- The state `zeroSignalTaylorSolution` solves the original Taylor system for a zero generator,
unit initial scalar, and zero source with parameters (1, 5, 1). -/
theorem zeroSignalTaylorSolution_solves :
    taylorStepMatrix 1 5 1 (0 : Matrix Unit Unit ℂ) *ᵥ zeroSignalTaylorSolution =
      taylorRHS 1 5 1 1 (fun _ : Unit => 1) 0 := by
  ext ⟨r, n⟩
  cases n
  fin_cases r <;>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Fintype.sum_unique] <;>
    norm_num [taylorStepMatrix, taylorRHS, zeroSignalTaylorSolution, Fin.ext_iff]

/-- The original zero-generator Taylor matrix with parameters (1, 5, 1) has entry 1 at row label
six and column label zero. -/
theorem zeroSignalTaylor_jump_entry :
    taylorStepMatrix 1 5 1 (0 : Matrix Unit Unit ℂ) (6, ()) (0, ()) = 1 := by
  norm_num [taylorStepMatrix, Fin.ext_iff]

/-- The scalar ODE with zero generator, zero source, and unit initial value has constant unit
solution. -/
theorem taylorODESolution_zero_signal (t : ℝ) :
    taylorODESolution (0 : Matrix Unit Unit ℂ) 0 (fun _ => 1) t = (fun _ => 1) := by
  have h := orderedForcedSolution_unique (fun _ => (0 : Matrix Unit Unit ℂ))
    (fun _ => (0 : QState Unit)) continuous_const continuous_const 0 (fun _ => 1)
    (fun _ => (fun _ : Unit => (1 : ℂ))) rfl (fun t => by
      simpa using! (hasDerivAt_const t (fun _ : Unit => (1 : ℂ))))
  simpa [taylorODESolution] using! (congrFun h t).symm

/-- Coherent extraction of `zeroSignalTaylorSolution` gives the constant scalar -2. -/
theorem zeroSignalTaylorSolution_extract :
    taylorExtract 1 5 1 zeroSignalTaylorSolution = (fun _ : Unit => -2) := by
  ext n
  norm_num [taylorExtract, zeroSignalTaylorSolution, Fin.sum_univ_succ]

/-- The final time block of `zeroSignalTaylorSolution` is the constant scalar -1. -/
theorem zeroSignalTaylorSolution_final :
    taylorBlock zeroSignalTaylorSolution (taylorTimeLabel 1 5 1 1 (by omega)) =
      (fun _ : Unit => -1) := by
  ext n
  norm_num [taylorBlock, taylorTimeLabel, zeroSignalTaylorSolution]

/-- Coherent extraction of the same-sign example gives the constant scalar 2. -/
theorem extractionSameSign_extract :
    taylorExtract 1 5 1 extractionSameSign = (fun _ : Unit => 2) := by
  ext n
  norm_num [taylorExtract, extractionSameSign, Fin.sum_univ_succ]

/-- The success-set mass of the same-sign example is 2. -/
theorem extractionSameSign_mass :
    MeasureProb extractionSameSign (taylorSuccessSet 1 5 1) = 2 := by
  norm_num [MeasureProb, BornProb, taylorSuccessSet, extractionSameSign,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The squared norm of the coherent extraction of the same-sign example is 4. -/
theorem extractionSameSign_extract_norm_sq :
    ‖stateVector (taylorExtract 1 5 1 extractionSameSign)‖ ^ 2 = 4 := by
  rw [extractionSameSign_extract, stateVector_norm_sq]
  norm_num [MeasureProb, BornProb]

/-- The squared norm of coherent extraction differs from the success-set mass for
`extractionSameSign`. -/
theorem extraction_mass_identity_counterexample :
    ‖stateVector (taylorExtract 1 5 1 extractionSameSign)‖ ^ 2 ≠
      MeasureProb extractionSameSign (taylorSuccessSet 1 5 1) := by
  rw [extractionSameSign_extract_norm_sq, extractionSameSign_mass]
  norm_num

/-- The opposite-sign example has zero coherent extraction. -/
theorem extractionOppositeSign_extract :
    taylorExtract 1 5 1 extractionOppositeSign = 0 := by
  ext n
  norm_num [taylorExtract, extractionOppositeSign, Fin.sum_univ_succ]

/-- The success-set mass of the opposite-sign example is 2. -/
theorem extractionOppositeSign_mass :
    MeasureProb extractionOppositeSign (taylorSuccessSet 1 5 1) = 2 := by
  norm_num [MeasureProb, BornProb, taylorSuccessSet, extractionOppositeSign,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

end Qatlib.Papers.QLinearODE17.StructureCore
