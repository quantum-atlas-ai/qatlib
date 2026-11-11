/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
import Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Same-wire physical capture and measured reuse

The existing Frozen fibre theorem transports the actual native words on the
complete register. First-capture cleanup preserves exactly one unknown spin
on its original storage wire before the next independent preparation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.SpinorSampling.Retained.PhysicalCapture
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
/-- The three physical wires carry the actual local amplitudes on the same spectator basis. -/
def physicalTripleState {n : ℕ} (a b c : Fin n) (z : Reg n)
    (φ : QState (Reg 3)) : QState (Reg n) :=
  ∑ u : Reg 3, φ u • Ket (tofEmb a b c u z)

/-- Exact reuse of the existing full-register fibre theorem for an actual native word. -/
theorem physicalTripleWord_run {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (full : List (MeasurementGate n)) (localWord : List (MeasurementGate 3))
    (hl : reflectionLegal (full.map measurementMatrix))
    (hw : ∀ g ∈ full.map measurementMatrix,reflectionGateWires g ⊆ {a,b,c})
    (hc : (full.map measurementMatrix).map (tofCoreGate a b c)=localWord.map measurementMatrix)
    (z : Reg n) (φ : QState (Reg 3)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measurementProgram full)
      (physicalTripleState a b c z φ) =
      physicalTripleState a b c z
        (Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (measurementProgram localWord) φ) := by
  unfold physicalTripleState measurementProgram
  rw [run_reflectionCompile_fibre a b c hab hac hbc _ hl hw z φ,hc,run_reflectionCompile]
  rfl

/-- The first actual full-register three-CX capture moves only the live unknown spin into its storage slot. -/
theorem physical_first_capture {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (u : Bool → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
      (physicalTripleState a b c z (captureTriple u (Ket false) (Ket false))) =
      physicalTripleState a b c z (captureTriple (Ket false) u (Ket false)) := by
  have hl : reflectionLegal ((captureSwapWord n a b).map measurementMatrix) := by
    intro g hg
    simp only [captureSwapWord,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl | rfl <;> simp [reflectionGateLegal,hab,Ne.symm hab]
  have hw : ∀ g ∈ (captureSwapWord n a b).map measurementMatrix,
      reflectionGateWires g ⊆ {a,b,c} := by
    intro g hg
    simp only [captureSwapWord,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl | rfl <;> simp [reflectionGateWires,Finset.subset_iff]
  have hc : ((captureSwapWord n a b).map measurementMatrix).map (tofCoreGate a b c)=
      (captureSwapWord 3 0 1).map measurementMatrix := by
    simp [captureSwapWord,measurementMatrix,nativeMatrix,tofCoreGate,tofCoreWire,Ne.symm hab]
  rw [captureSwapProgram,physicalTripleWord_run a b c hab hac hbc _ _ hl hw hc]
  change physicalTripleState a b c z
    (Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 1)
      (captureTriple u (Ket false) (Ket false))) = _
  rw [first_capture_clean]

/-- The second actual full-register capture moves the fresh live spin into slot two and preserves the retained first spin. -/
theorem physical_second_capture {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (u v : Bool → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a c)
      (physicalTripleState a b c z (captureTriple v u (Ket false))) =
      physicalTripleState a b c z (captureTriple (Ket false) u v) := by
  have hl : reflectionLegal ((captureSwapWord n a c).map measurementMatrix) := by
    intro g hg
    simp only [captureSwapWord,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl | rfl <;> simp [reflectionGateLegal,hac,Ne.symm hac]
  have hw : ∀ g ∈ (captureSwapWord n a c).map measurementMatrix,
      reflectionGateWires g ⊆ {a,b,c} := by
    intro g hg
    simp only [captureSwapWord,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl | rfl <;> simp [reflectionGateWires,Finset.subset_iff]
  have hc : ((captureSwapWord n a c).map measurementMatrix).map (tofCoreGate a b c)=
      (captureSwapWord 3 0 2).map measurementMatrix := by
    simp [captureSwapWord,measurementMatrix,nativeMatrix,tofCoreGate,tofCoreWire,Ne.symm hac,Ne.symm hbc]
  rw [captureSwapProgram,physicalTripleWord_run a b c hab hac hbc _ _ hl hw hc]
  change physicalTripleState a b c z
    (Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 2)
      (captureTriple v u (Ket false))) = _
  rw [second_capture_preserves_first]


/-- The canonical three-bit coordinate equivalence only enumerates the local mathematical fibre. -/
def captureTripleEquiv : (Bool × Bool × Bool) ≃ Reg 3 where
  toFun p := captureReg p.1 p.2.1 p.2.2
  invFun u := (u 0,u 1,u 2)
  left_inv p := by rcases p with ⟨a,b,c⟩; rfl
  right_inv u := by funext i; fin_cases i <;> rfl

/-- After capture the full state has just one unknown spin on its original fixed storage wire. -/
theorem physical_first_stored_fibre {n : ℕ} (a b c : Fin n) (z : Reg n) (u : Bool → ℂ) :
    physicalTripleState a b c z (captureTriple (Ket false) u (Ket false)) =
      ∑ s : Bool, u s • Ket (tofEmb a b c (captureReg false s false) z) := by
  unfold physicalTripleState
  rw [← Fintype.sum_equiv captureTripleEquiv
    (fun p => captureTriple (Ket false) u (Ket false) (captureTripleEquiv p) •
      Ket (tofEmb a b c (captureTripleEquiv p) z))
    (fun v => captureTriple (Ket false) u (Ket false) v • Ket (tofEmb a b c v z))
    (fun _ => rfl)]
  simp [Fintype.sum_prod_type,captureTripleEquiv,captureTriple,
    Qatlib.Foundations.PureStateMath.Ket]

/-- Replacing the single stored bit in the same physical basis uses no gate or address relocation. -/
theorem physical_stored_register_update {n : ℕ} (a b c : Fin n) (hab : a≠b)
    (z : Reg n) (s : Bool) :
    tofEmb a b c (captureReg false s false) z =
      Function.update (tofEmb a b c (captureReg false false false) z) b s := by
  funext k
  by_cases hkb : k=b
  · subst k
    simp [tofEmb,Ne.symm hab]
  · simp only [Function.update_of_ne hkb,tofEmb,ite_eq_right hkb]
    by_cases hka : k=a
    · simp [hka]
    · by_cases hkc : k=c <;> simp [hka,hkc]


/-- Full-register first capture and actual measured cleanup retain exactly the same unknown coherent spin. -/
theorem physical_first_capture_cleanup {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (u : Bool → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (measuredClearProgram (retainedCleanupWires b)
        (tofEmb a b c (captureReg false false false) z))
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
        (physicalTripleState a b c z (captureTriple u (Ket false) (Ket false)))) =
      ∑ s : Bool, u s • Ket (Function.update (fun _ : Fin n => false) b s) := by
  rw [physical_first_capture a b c hab hac hbc,physical_first_stored_fibre]
  have hs : (∑ s : Bool, u s • Ket (tofEmb a b c (captureReg false s false) z)) =
      ∑ s : Bool, u s • Ket (Function.update
        (tofEmb a b c (captureReg false false false) z) b s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [physical_stored_register_update a b c hab]
  rw [hs]
  rw [measuredClearProgram_quantum_retained _ _ (retainedCleanupWires_omits b)]
  have hz : tofEmb a b c (captureReg false false false) z b=false := by
    simp [tofEmb,Ne.symm hab]
  rw [retainedCleanupBits_zero b _ hz]



/-- The listed cleanup measurement really occurs after the first capture and does not observe the retained spin. -/
theorem physical_first_capture_cleanup_measurement {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (u : Bool → ℂ) :
    ApplyGate (measuredMaskMatrix (retainedCleanupWires b)
      (tofEmb a b c (captureReg false false false) z))
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
        (physicalTripleState a b c z (captureTriple u (Ket false) (Ket false)))) =
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
        (physicalTripleState a b c z (captureTriple u (Ket false) (Ket false))) := by
  simp only [physical_first_capture a b c hab hac hbc,physical_first_stored_fibre]
  have hs : (∑ s : Bool,u s • Ket (tofEmb a b c (captureReg false s false) z))=
      ∑ s : Bool,u s • Ket (Function.update
        (tofEmb a b c (captureReg false false false) z) b s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [physical_stored_register_update a b c hab]
  simp only [hs]
  exact measuredMaskMatrix_quantum_retained _ b (retainedCleanupWires_omits b) _ u

/-- The actual spectator measurement and conditional native correction together preserve one unknown spin and clear every other full-register wire. -/
theorem physical_first_capture_measured_cleanup {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (u : Bool → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (measuredClearProgram (retainedCleanupWires b)
        (tofEmb a b c (captureReg false false false) z))
      (ApplyGate (measuredMaskMatrix (retainedCleanupWires b)
        (tofEmb a b c (captureReg false false false) z))
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
          (physicalTripleState a b c z (captureTriple u (Ket false) (Ket false))))) =
      ∑ s : Bool,u s • Ket (Function.update (fun _ : Fin n => false) b s) := by
  rw [physical_first_capture_cleanup_measurement a b c hab hac hbc]
  exact physical_first_capture_cleanup a b c hab hac hbc z u


end Qatlib.Concepts.SpinorSampling.Retained.PhysicalCapture
