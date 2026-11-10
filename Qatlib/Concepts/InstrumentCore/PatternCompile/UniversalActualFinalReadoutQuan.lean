/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalActualFinalReadoutStat
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalReadoutAux
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalRawFrameReadoutQuan
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

private theorem sum_filter {α : Type*} (ls : List α) (p : α → Bool) (f : α → ℝ) :
    ((ls.filter p).map f).sum=(ls.map (fun x => if p x then f x else 0)).sum := by
  induction ls with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

theorem mbqcDensityEvent_diagonal {D : ℕ} (ρ : Operator D) (E : Finset (Fin D)) :
    mbqcDensityEvent ρ E=∑ y : Fin D, if y ∈ E then (ρ y y).re else 0 := by
  simp [mbqcDensityEvent,Matrix.trace,Matrix.diag_apply,Projector,Matrix.diagonal_mul]

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

theorem universalActualFinalReadout_answer : UniversalActualFinalReadout := by
  intro n L G hlegal E
  refine ⟨mbqcReadoutProgram_wellFormed G hlegal E,mbqcReadoutProgram_leafCount G E,
    mbqcReadoutLeaf_fields G E,?_⟩
  intro ρ hρ
  refine ⟨mbqcPhysicalInput_density G ρ hρ,?_⟩
  rw [mbqcReadoutAcceptance_decoded G hlegal]
  exact (universalRawFrameReadout_answer n L G hlegal).2.2.2.2 ρ hρ E |>.2

end Qatlib.Concepts.InstrumentCore.PatternCompile
