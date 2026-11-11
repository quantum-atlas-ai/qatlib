/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalActualFinalReadoutStat
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalReadoutAux
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalRawFrameReadoutQuan

/-!
# Correctness of actual graph-state final readout

This module connects physical final-readout leaf masses to diagonal entries of raw graph-state
branches. `mbqcReadoutAcceptance_decoded` expresses acceptance as a sum over branch events
decoded by their final Pauli frames.

`universalActualFinalReadout_answer` proves the complete final-readout specification, combining
well-formedness and resource fields with equality of physical acceptance and logical output
event probabilities in the measurement scheme of [RaussendorfBriegel2000].

## Main statements

* `mbqcReadoutLeaf_mass`: the diagonal formula for physical leaf mass.
* `mbqcReadoutAcceptance_decoded`: acceptance as a sum of decoded branch events.
* `universalActualFinalReadout_answer`: the complete actual final-readout specification.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- Summing a real-valued function over a filtered list equals summing its values on accepted
entries and zero on the others. -/
private theorem sum_filter {α : Type*} (ls : List α) (p : α → Bool) (f : α → ℝ) :
    ((ls.filter p).map f).sum=(ls.map (fun x => if p x then f x else 0)).sum := by
  induction ls with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

/-- The density-event value is the sum of real diagonal entries at outcomes in the event. -/
theorem mbqcDensityEvent_diagonal {D : ℕ} (ρ : Operator D) (E : Finset (Fin D)) :
    mbqcDensityEvent ρ E=∑ y : Fin D, if y ∈ E then (ρ y y).re else 0 := by
  simp [mbqcDensityEvent,Matrix.trace,Matrix.diag_apply,Projector,Matrix.diagonal_mul]

/-- For a legal graph word, the mixed mass of a physical final-readout leaf equals the real
diagonal entry of its raw branch at the measured outcome. -/
theorem mbqcReadoutLeaf_mass {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (E : Finset (Fin (2^n)))
    (h : GraphHistory G) (y : Fin (2^n)) (ρ : Operator (2^n)) :
    mixedMass (leafMixedTrace (mbqcReadoutLeaf G E h y) (mbqcPhysicalInput G ρ))=
      (mbqcRawBranch G h ρ y y).re := by
  change (Matrix.trace ((mbqcReadoutLeaf G E h y).operator*mbqcPhysicalInput G ρ*
    (mbqcReadoutLeaf G E h y).operatorᴴ)).re=_
  rw [(mbqcReadoutLeaf_fields G E h y).2.1,Matrix.conjTranspose_mul,projector_conjTranspose]
  rw [mbqcRawBranch_discard]
  congr 1
  have he := mbqcOutputLabel_mass G hlegal
    ((mbqcRawLeaf G h).operator*mbqcPhysicalInput G ρ*(mbqcRawLeaf G h).operatorᴴ) y
  simpa only [Matrix.mul_assoc] using! he

/-- For a legal graph word, physical readout acceptance is the sum of raw-branch event values
for events decoded by the corresponding final Pauli frames. -/
theorem mbqcReadoutAcceptance_decoded {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (E : Finset (Fin (2^n))) (ρ : Operator (2^n)) :
    mbqcReadoutAcceptance G E ρ=∑ h : GraphHistory G,
      mbqcDensityEvent (mbqcRawBranch G h ρ) (mbqcDecodedEvent (graphFinalFrame G h) E) := by
  unfold mbqcReadoutAcceptance
  rw [sum_filter,(observedMixedTraces_leaf_correspondence 1 (mbqcReadoutProgram G E)
    (mbqcPhysicalInput G ρ)).1,List.map_ofFn,List.sum_ofFn]
  let e := Equiv.ofBijective (mbqcReadoutIndex G E) (mbqcReadoutIndex_bijective G E)
  rw [← e.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [mbqcDensityEvent_diagonal]
  apply Finset.sum_congr rfl
  intro y _
  change (if (leafMixedTrace (observedLeaf 1 (mbqcReadoutProgram G E)
    (mbqcReadoutIndex G E (h,y))) (mbqcPhysicalInput G ρ)).accepted then
      mixedMass (leafMixedTrace (observedLeaf 1 (mbqcReadoutProgram G E)
        (mbqcReadoutIndex G E (h,y))) (mbqcPhysicalInput G ρ)) else 0)=_
  rw [mbqcReadoutLeaf_observedLeaf]
  change (if (mbqcReadoutLeaf G E h y).accepted then
    mixedMass (leafMixedTrace (mbqcReadoutLeaf G E h y) (mbqcPhysicalInput G ρ)) else 0)=_
  rw [(mbqcReadoutLeaf_fields G E h y).2.2.1,mbqcReadoutLeaf_mass G hlegal]
  simp [mbqcDecodedEvent]

/-- Every legal graph word satisfies the actual final-readout specification, including
well-formedness, exact leaf resources, and agreement of acceptance probabilities with the
logical circuit on density inputs [RaussendorfBriegel2000]. -/
theorem universalActualFinalReadout_answer : UniversalActualFinalReadout := by
  intro n L G hlegal E
  refine ⟨mbqcReadoutProgram_wellFormed G hlegal E,mbqcReadoutProgram_leafCount G E,
    mbqcReadoutLeaf_fields G E,?_⟩
  intro ρ hρ
  refine ⟨mbqcPhysicalInput_density G ρ hρ,?_⟩
  rw [mbqcReadoutAcceptance_decoded G hlegal]
  exact (universalRawFrameReadout_answer n L G hlegal).2.2.2.2 ρ hρ E |>.2

end Qatlib.Concepts.InstrumentCore.PatternCompile
