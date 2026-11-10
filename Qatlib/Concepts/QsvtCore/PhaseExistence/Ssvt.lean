/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SsvtDefs
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.QsVtMain

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators Kronecker

theorem def15Steps_odd (Φ : List ℝ) :
    def15Steps Φ .odd = cppCompile (sourceRealFamily Φ) := rfl

theorem def15Steps_even (Φ : List ℝ) :
    def15Steps Φ .even = (cppCompile (sourceRealFamily Φ)).map cppSwapData := rfl

theorem def15Word_odd (Φ : List ℝ) {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (hodd : Φ.length % 2 = 1) :
    def15Word U P Q Φ .odd = sourceRealWord U P Q Φ := by
  show cppEvaluate U P Q (def15Steps Φ .odd) = sourceRealWord U P Q Φ
  rw [def15Steps_odd]
  show cppEvaluate U P Q (cppCompile (sourceRealFamily Φ)) = sourceRealWord U P Q Φ
  unfold sourceRealWord
  rw [if_pos hodd]

theorem def15Word_even (Φ : List ℝ) {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (heven : Φ.length % 2 = 0) :
    def15Word U P Q Φ .even = sourceRealWord U P Q Φ := by
  show cppEvaluate U Q P (def15Steps Φ .even) = sourceRealWord U P Q Φ
  rw [def15Steps_even]
  show cppEvaluate U Q P ((cppCompile (sourceRealFamily Φ)).map cppSwapData) =
    sourceRealWord U P Q Φ
  unfold sourceRealWord
  have hne : Φ.length % 2 ≠ 1 := by omega
  rw [if_neg hne]

theorem def15Word_eq_sourceRealWord (Φ : List ℝ) {H : Type} [Fintype H]
    [DecidableEq H] (U P Q : Matrix H H ℂ) :
    def15Word U P Q Φ (if Φ.length % 2 = 1 then Def15Parity.odd else Def15Parity.even) =
      sourceRealWord U P Q Φ := by
  split
  · rename_i h
    exact def15Word_odd Φ U P Q h
  · rename_i h
    have heven : Φ.length % 2 = 0 := by omega
    exact def15Word_even Φ U P Q heven

theorem def15Ledger_cppCompile {J : Type} (fs : List (J → ℝ)) :
    def15Ledger (cppCompile fs) =
      { forwardQueries := (fs.length + 1) / 2
        adjointQueries := fs.length / 2
        projectorNotP := 2 * (fs.length / 2)
        projectorNotQ := 2 * ((fs.length + 1) / 2)
        phaseMacros := fs.length } := by
  induction fs with
  | nil => simp [cppCompile, def15Ledger]
  | cons f fs ih =>
    rw [cppCompile, def15Ledger_append, def15Ledger_swap, ih]
    simp only [List.length_cons]
    simp [def15Ledger]
    omega

theorem def15_ledger (Φ : List ℝ) :
    def15Ledger (def15Steps Φ .odd) =
      { forwardQueries := (Φ.length + 1) / 2
        adjointQueries := Φ.length / 2
        projectorNotP := 2 * (Φ.length / 2)
        projectorNotQ := 2 * ((Φ.length + 1) / 2)
        phaseMacros := Φ.length } := by
  have hlen : (sourceRealFamily Φ).length = Φ.length := by
    simp [sourceRealFamily]
  rw [def15Steps_odd, def15Ledger_cppCompile, hlen]

theorem def15_ledger_even (Φ : List ℝ) :
    def15Ledger (def15Steps Φ .even) =
      { forwardQueries := Φ.length / 2
        adjointQueries := (Φ.length + 1) / 2
        projectorNotP := 2 * (Φ.length / 2)
        projectorNotQ := 2 * ((Φ.length + 1) / 2)
        phaseMacros := Φ.length } := by
  rw [def15Steps_even, def15Ledger_swapData, def15Ledger_cppCompile]
  have hlen : (sourceRealFamily Φ).length = Φ.length := by
    simp [sourceRealFamily]
  rw [hlen]

theorem def15_ledger_both (Φ : List ℝ) :
    def15Ledger (def15Steps Φ .even) =
      { forwardQueries := Φ.length / 2
        adjointQueries := (Φ.length + 1) / 2
        projectorNotP := 2 * (Φ.length / 2)
        projectorNotQ := 2 * ((Φ.length + 1) / 2)
        phaseMacros := Φ.length } ∧
    def15Ledger (def15Steps Φ .odd) =
      { forwardQueries := (Φ.length + 1) / 2
        adjointQueries := Φ.length / 2
        projectorNotP := 2 * (Φ.length / 2)
        projectorNotQ := 2 * ((Φ.length + 1) / 2)
        phaseMacros := Φ.length } :=
  ⟨def15_ledger_even Φ, def15_ledger Φ⟩

theorem def15_parity_endpoints (d : ℕ) :
    (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
    (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
    (2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; omega
  · intro h; omega
  · omega

theorem def15_ledger_components (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).forwardQueries = (Φ.length + 1) / 2 ∧
    (def15Ledger (def15Steps Φ .odd)).adjointQueries = Φ.length / 2 ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).phaseMacros = Φ.length := by
  rw [def15_ledger]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem def15_ledger_components_even (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .even)).forwardQueries = Φ.length / 2 ∧
    (def15Ledger (def15Steps Φ .even)).adjointQueries = (Φ.length + 1) / 2 ∧
    (def15Ledger (def15Steps Φ .even)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .even)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (def15Ledger (def15Steps Φ .even)).phaseMacros = Φ.length := by
  rw [def15_ledger_even]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem def15_projectorNot_classes (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (Φ.length % 2 = 0 → 2 * (Φ.length / 2) = Φ.length) ∧
    (Φ.length % 2 = 1 → 2 * (Φ.length / 2) = Φ.length - 1) := by
  obtain ⟨_, _, hP, hQ, _⟩ := def15_ledger_components Φ
  refine ⟨hP, hQ, ?_, ?_⟩
  · intro hpar; omega
  · intro hpar; omega

theorem def15_projectorNot_total (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).projectorNotP +
        (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * Φ.length := by
  obtain ⟨_, _, hP, hQ, _⟩ := def15_ledger_components Φ
  omega

theorem def15_dataQueries (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).forwardQueries +
        (def15Ledger (def15Steps Φ .odd)).adjointQueries = Φ.length := by
  obtain ⟨hF, hA, _, _, _⟩ := def15_ledger_components Φ
  omega

theorem ctrlCounts_ctrlCompileControlled {J : Type} (fs : List (J → ℝ)) :
    ctrlCounts (ctrlCompileControlled fs) =
      { dataQueries := (fs.length + 1) / 2
        adjointQueries := fs.length / 2
        projectorNots := 2 * (fs.length / 2) + 2 * ((fs.length + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := fs.length
        multiplyControlledPhaseGates := 0
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  induction fs with
  | nil => simp [ctrlCompileControlled, ctrlCounts]
  | cons f fs ih =>
    rw [ctrlCompileControlled, ctrlCounts_append, ctrlCounts_swap, ih]
    simp only [List.length_cons]
    simp [ctrlCounts]
    omega

theorem ctrlCounts_ctrlCompileMultiplyControlled {J : Type} (fs : List (J → ℝ)) :
    ctrlCounts (ctrlCompileMultiplyControlled fs) =
      { dataQueries := (fs.length + 1) / 2
        adjointQueries := fs.length / 2
        projectorNots := 2 * (fs.length / 2) + 2 * ((fs.length + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := 0
        multiplyControlledPhaseGates := fs.length
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  induction fs with
  | nil => simp [ctrlCompileMultiplyControlled, ctrlCounts]
  | cons f fs ih =>
    rw [ctrlCompileMultiplyControlled, ctrlCounts_append, ctrlCounts_swap, ih]
    simp only [List.length_cons]
    simp [ctrlCounts]
    omega

theorem ctrlDef15_ledger_odd (Φ : List ℝ) :
    ctrlCounts (ctrlDef15Steps Φ .odd) =
      { dataQueries := (Φ.length + 1) / 2
        adjointQueries := Φ.length / 2
        projectorNots := 2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := Φ.length
        multiplyControlledPhaseGates := 0
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  have hlen : (ctrlSourceFamily Φ).length = Φ.length := by
    simp [ctrlSourceFamily, sourceRealFamily]
  rw [ctrlDef15Steps, ctrlCounts_ctrlCompileControlled, hlen]

theorem ctrlDef15_ledger_even (Φ : List ℝ) :
    ctrlCounts (ctrlDef15Steps Φ .even) =
      { dataQueries := Φ.length / 2
        adjointQueries := (Φ.length + 1) / 2
        projectorNots := 2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := Φ.length
        multiplyControlledPhaseGates := 0
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  have hlen : (ctrlSourceFamily Φ).length = Φ.length := by
    simp [ctrlSourceFamily, sourceRealFamily]
  rw [ctrlDef15Steps, ctrlCounts_swapData, ctrlCounts_ctrlCompileControlled, hlen]

theorem mulCtrlDef15_ledger_odd {m : ℕ} (Φs : List (List ℝ)) (d : ℕ) :
    ctrlCounts (mulCtrlDef15Steps m Φs d .odd) =
      { dataQueries := (d + 1) / 2
        adjointQueries := d / 2
        projectorNots := 2 * (d / 2) + 2 * ((d + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := 0
        multiplyControlledPhaseGates := d
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  have hlen : (mulCtrlSourceFamily (m := m) Φs d).length = d := by
    simp [mulCtrlSourceFamily]
  rw [mulCtrlDef15Steps, ctrlCounts_ctrlCompileMultiplyControlled, hlen]

theorem mulCtrlDef15_ledger_even {m : ℕ} (Φs : List (List ℝ)) (d : ℕ) :
    ctrlCounts (mulCtrlDef15Steps m Φs d .even) =
      { dataQueries := d / 2
        adjointQueries := (d + 1) / 2
        projectorNots := 2 * (d / 2) + 2 * ((d + 1) / 2)
        phaseGates := 0
        controlledPhaseGates := 0
        multiplyControlledPhaseGates := d
        controlledDataQueries := 0
        controlledAdjointQueries := 0 } := by
  have hlen : (mulCtrlSourceFamily (m := m) Φs d).length = d := by
    simp [mulCtrlSourceFamily]
  rw [mulCtrlDef15Steps, ctrlCounts_swapData, ctrlCounts_ctrlCompileMultiplyControlled, hlen]

theorem ctrlDef15_ledger_components_odd (Φ : List ℝ) :
    (ctrlCounts (ctrlDef15Steps Φ .odd)).dataQueries = (Φ.length + 1) / 2 ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).adjointQueries = Φ.length / 2 ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).projectorNots =
      2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2) ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledPhaseGates = Φ.length ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledDataQueries = 0 := by
  rw [ctrlDef15_ledger_odd]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mulCtrlDef15_ledger_components_odd {m : ℕ} (Φs : List (List ℝ))
    (d : ℕ) :
    (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).dataQueries = (d + 1) / 2 ∧
    (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).adjointQueries = d / 2 ∧
    (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).projectorNots =
      2 * (d / 2) + 2 * ((d + 1) / 2) ∧
    (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).multiplyControlledPhaseGates = d ∧
    (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).controlledDataQueries = 0 := by
  rw [mulCtrlDef15_ledger_odd (m := m) Φs d]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem clause76_endpoint :

    (∀ (Φ : List ℝ) {H : Type} [Fintype H] [DecidableEq H]
        (U P Q : Matrix H H ℂ) (hodd : Φ.length % 2 = 1),
        def15Word U P Q Φ .odd = sourceRealWord U P Q Φ ∧
        def15Ledger (def15Steps Φ .odd) =
          { forwardQueries := (Φ.length + 1) / 2
            adjointQueries := Φ.length / 2
            projectorNotP := 2 * (Φ.length / 2)
            projectorNotQ := 2 * ((Φ.length + 1) / 2)
            phaseMacros := Φ.length }) ∧

    (∀ (Φ : List ℝ) {H : Type} [Fintype H] [DecidableEq H]
        (U P Q : Matrix H H ℂ) (heven : Φ.length % 2 = 0),
        def15Word U P Q Φ .even = sourceRealWord U P Q Φ ∧
        def15Ledger (def15Steps Φ .even) =
          { forwardQueries := Φ.length / 2
            adjointQueries := (Φ.length + 1) / 2
            projectorNotP := 2 * (Φ.length / 2)
            projectorNotQ := 2 * ((Φ.length + 1) / 2)
            phaseMacros := Φ.length }) ∧

    (∀ d : ℕ,
        (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
        (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
        (2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d)) ∧

    (∀ (Φ : List ℝ),
        ctrlCounts (ctrlDef15Steps Φ .odd) =
          { dataQueries := (Φ.length + 1) / 2
            adjointQueries := Φ.length / 2
            projectorNots := 2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2)
            phaseGates := 0
            controlledPhaseGates := Φ.length
            multiplyControlledPhaseGates := 0
            controlledDataQueries := 0
            controlledAdjointQueries := 0 } ∧
        ctrlCounts (ctrlDef15Steps Φ .even) =
          { dataQueries := Φ.length / 2
            adjointQueries := (Φ.length + 1) / 2
            projectorNots := 2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2)
            phaseGates := 0
            controlledPhaseGates := Φ.length
            multiplyControlledPhaseGates := 0
            controlledDataQueries := 0
            controlledAdjointQueries := 0 }) ∧

    (∀ (m : ℕ) (Φs : List (List ℝ)) (d : ℕ),
        ctrlCounts (mulCtrlDef15Steps m Φs d .odd) =
          { dataQueries := (d + 1) / 2
            adjointQueries := d / 2
            projectorNots := 2 * (d / 2) + 2 * ((d + 1) / 2)
            phaseGates := 0
            controlledPhaseGates := 0
            multiplyControlledPhaseGates := d
            controlledDataQueries := 0
            controlledAdjointQueries := 0 } ∧
        ctrlCounts (mulCtrlDef15Steps m Φs d .even) =
          { dataQueries := d / 2
            adjointQueries := (d + 1) / 2
            projectorNots := 2 * (d / 2) + 2 * ((d + 1) / 2)
            phaseGates := 0
            controlledPhaseGates := 0
            multiplyControlledPhaseGates := d
            controlledDataQueries := 0
            controlledAdjointQueries := 0 }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Φ H _ _ U P Q hodd
    refine ⟨def15Word_odd Φ U P Q hodd, ?_⟩
    exact def15_ledger Φ
  · intro Φ H _ _ U P Q heven
    refine ⟨def15Word_even Φ U P Q heven, ?_⟩
    exact def15_ledger_even Φ
  · exact def15_parity_endpoints
  · intro Φ
    exact ⟨ctrlDef15_ledger_odd Φ, ctrlDef15_ledger_even Φ⟩
  · intro m Φs d
    exact ⟨mulCtrlDef15_ledger_odd (m := m) Φs d, mulCtrlDef15_ledger_even (m := m) Φs d⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence
