/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.MagnitudeFlag
public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

@[expose] public section

/-!
# A common clock for stencil phase tests

[ChenXueChenEtAl2022], Appendix C.3, refers to the phased variable-time
procedure of [ChildsKothariSomma2017], Section 5. Each step of the common
clock has its own decision bit and phase workspace, which may have a
different dimension at each step. Routing to the current step's registers
preserves prior decisions. Steps act as the identity on a history that
accepted at an earlier step. The reciprocal and amplification stages are
separate from the ordered decision program.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath (ApplyGate Ket QState TensorState applyGate_one ket_apply)
open Qatlib.Foundations.QueryWordCore.Circuit (Circuit IsUnitaryCircuit Run Step run_gate)
open Qatlib.Foundations.PureStateMath.BornBridge (applyGate_relabelGate relabelGate relabelState)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open scoped Classical

variable {n : ℕ} {I : Type}

/-- The decision bit, phase counter, and internal phase flag of one clock step. -/
abbrev PhaseTapeSlot (width : ℕ) := Bool × (Fin width × Bool)

/-- The fixed clock stores phase counters of each step's own width. -/
abbrev PhaseTape (width : Fin n → ℕ) := (s : Fin n) → PhaseTapeSlot (width s)

/-- The clock tape with the current step removed. -/
abbrev RemainingPhaseTape (width : Fin n → ℕ) (t : Fin n) :=
  (s : {s : Fin n // s ≠ t}) → PhaseTapeSlot (width s.val)

/-- Peel the current step's registers out of the dependent product. -/
def splitPhaseTape (width : Fin n → ℕ) (t : Fin n) :
    PhaseTape width ≃ RemainingPhaseTape width t × PhaseTapeSlot (width t) where
  toFun tape := (fun s => tape s.val, tape t)
  invFun parts s := if h : s = t then h.symm ▸ parts.2 else parts.1 ⟨s, h⟩
  left_inv tape := by
    funext s
    by_cases hs : s = t
    · subst s
      simp
    · simp [hs]
  right_inv := by
    rintro ⟨other, here⟩
    apply Prod.ext
    · funext s
      simp [s.property]
    · simp

/-- Route the current decision bit and its phase workspace next to the shared signal. -/
def focusPhaseTape (width : Fin n → ℕ) (t : Fin n) :
    PhaseTape width × I ≃ RemainingPhaseTape width t × (Bool × (Fin (width t) × (Bool × I))) :=
  (Equiv.prodCongr (splitPhaseTape width t) (Equiv.refl I)).trans
    ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _)))))

/-- The clock is stopped before this step exactly when an earlier slot has accepted. -/
def phaseTapeStopped (width : Fin n → ℕ) (t : Fin n) (history : RemainingPhaseTape width t) : Prop :=
  ∃ s, s.val < t ∧ (history s).1 = true

variable [Fintype I] [DecidableEq I]

/-- The step performs the threshold decision on its routed workspace only if no earlier
decision bit has accepted. -/
def routedMagnitudeStage (width : Fin n → ℕ) (t : Fin n) (U : Matrix I I ℂ) (threshold : ℝ) :
    Matrix (PhaseTape width × I) (PhaseTape width × I) ℂ :=
  relabelGate (focusPhaseTape (I := I) width t).symm
    (blockDiagFirst fun history =>
      if phaseTapeStopped width t history then 1 else countedMagnitudeFlag U (width t) threshold)

/-- The routed stage is unitary for a unitary walk and a nonempty current counter. -/
theorem routed_magnitude_stage_unitary (width : Fin n → ℕ) (t : Fin n) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hWidth : 0 < width t) (threshold : ℝ) :
    routedMagnitudeStage width t U threshold ∈ Matrix.unitaryGroup _ ℂ := by
  unfold routedMagnitudeStage
  apply relabelGate_mem_unitary
  apply blockDiagFirst_unitary
  intro history
  split_ifs
  · exact Submonoid.one_mem _
  · exact counted_magnitude_flag_unitary U hU (width t) hWidth threshold

/-- Every amplitude with an earlier acceptance is exactly fixed on the original clock,
independently of the signal and other clock components. -/
theorem routed_magnitude_stage_stopped (width : Fin n → ℕ) (t : Fin n) (U : Matrix I I ℂ)
    (threshold : ℝ) (ψ : QState (PhaseTape width × I)) (tape : PhaseTape width) (signal : I)
    (stopped : ∃ s, s < t ∧ (tape s).1 = true) :
    ApplyGate (routedMagnitudeStage width t U threshold) ψ (tape, signal) = ψ (tape, signal) := by
  let e := focusPhaseTape (I := I) width t
  let blocks (history : RemainingPhaseTape width t) :=
    if phaseTapeStopped width t history then 1 else countedMagnitudeFlag U (width t) threshold
  have hInput : relabelState e.symm (relabelState e ψ) = ψ := by
    funext p
    simp [relabelState]
  change ApplyGate (relabelGate e.symm (blockDiagFirst blocks)) ψ (tape, signal) = _
  conv_lhs => rw [← hInput, applyGate_relabelGate]
  change ApplyGate (blockDiagFirst blocks) (relabelState e ψ) (e (tape, signal)) = _
  have hStop : phaseTapeStopped width t (e (tape, signal)).1 := by
    obtain ⟨s, hs, ha⟩ := stopped
    exact ⟨⟨s, ne_of_lt hs⟩, hs, ha⟩
  rw [applyGate_blockDiagFirst_slice]
  simp only [blocks, ite_eq_left hStop, applyGate_one, relabelState, Function.comp_apply, e.symm_apply_apply]

/-- A running history stays fixed while the current decision acts on its local state. -/
theorem routed_magnitude_stage_running (width : Fin n → ℕ) (t : Fin n) (U : Matrix I I ℂ)
    (threshold : ℝ) (history : RemainingPhaseTape width t) (hRunning : ¬phaseTapeStopped width t history)
    (ψ : QState (Bool × (Fin (width t) × (Bool × I)))) :
    let e := focusPhaseTape (I := I) width t
    ApplyGate (routedMagnitudeStage width t U threshold) (relabelState e.symm (TensorState (Ket history) ψ)) =
      relabelState e.symm (TensorState (Ket history) (ApplyGate (countedMagnitudeFlag U (width t) threshold) ψ)) := by
  intro e
  unfold routedMagnitudeStage
  rw [applyGate_relabelGate]
  congr 1
  funext p
  obtain ⟨observed, work⟩ := p
  rw [applyGate_blockDiagFirst_slice]
  by_cases ho : observed = history
  · subst observed
    rw [ite_eq_right hRunning]
    have hSlice : (fun q => TensorState (Ket history) ψ (history, q)) = ψ := by
      funext q
      simp [TensorState]
    rw [hSlice]
    simp [TensorState]
  · have hSlice : (fun q => TensorState (Ket history) ψ (observed, q)) = 0 := by
      funext q
      simp [TensorState, ket_apply, ho]
    rw [hSlice]
    simp [ApplyGate, TensorState, ket_apply, ho]

/-- Execute the scheduled magnitude tests in increasing clock order. -/
def stencilPhaseProgram (width : Fin n → ℕ) (threshold : Fin n → ℝ) (U : Matrix I I ℂ) :
    Circuit (PhaseTape width × I) :=
  (List.finRange n).map fun t => Step.gate (routedMagnitudeStage width t U (threshold t))

/-- Each stage in the ordered decision program is unitary. -/
theorem stencil_phase_program_unitary (width : Fin n → ℕ) (threshold : Fin n → ℝ)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (hWidth : ∀ t, 0 < width t) :
    IsUnitaryCircuit (stencilPhaseProgram width threshold U) := by
  intro G hG
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hG
  rw [← Step.gate.inj ht]
  exact routed_magnitude_stage_unitary width t U hU (hWidth t) (threshold t)

/-- Every suffix of tests strictly after an accepted step fixes that tape's amplitudes. -/
theorem later_stencil_phases_fix_accepted (width : Fin n → ℕ) (threshold : Fin n → ℝ)
    (U : Matrix I I ℂ) (oracle : Matrix (PhaseTape width × I) (PhaseTape width × I) ℂ)
    (tape : PhaseTape width) (signal : I) (accepted : Fin n) (hAccepted : (tape accepted).1 = true)
    (later : List (Fin n)) (hLater : ∀ t ∈ later, accepted < t) (ψ : QState (PhaseTape width × I)) :
    Run oracle (later.map fun t => Step.gate (routedMagnitudeStage width t U (threshold t)))
      ψ (tape, signal) = ψ (tape, signal) := by
  induction later generalizing ψ with
  | nil => rfl
  | cons t later ih =>
    simp only [List.map_cons, run_gate]
    calc
      _ = ApplyGate (routedMagnitudeStage width t U (threshold t)) ψ (tape, signal) := by
        apply ih
        intro u hu
        exact hLater u (List.mem_cons_of_mem t hu)
      _ = _ := routed_magnitude_stage_stopped width t U (threshold t) ψ tape signal
        ⟨accepted, hLater t List.mem_cons_self, hAccepted⟩

end Qatlib.Papers.QFVMChen22.TimeStep
