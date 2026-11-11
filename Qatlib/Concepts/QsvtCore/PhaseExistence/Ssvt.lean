/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SsvtDefs

/-!
# Singular value transformation words and resource counts

`def15Word_eq_sourceRealWord` identifies the parity-selected word with `sourceRealWord`. The
module computes the exact forward and adjoint query counts, the two projector-NOT counts, and
the phase counts of the corresponding compiled step lists.

Controlled and multiply controlled variants have analogous ledgers with controlled phase
operations and zero controlled data-query counts. `clause76_endpoint` collects the word
identities, parity arithmetic, and resource formulas. See [GilyenSuLowWiebe2019].

## Main statements

* `def15Word_eq_sourceRealWord`: identify the parity-selected matrix word.
* `def15_ledger_both`: compute the two parity ledgers.
* `ctrlDef15_ledger_odd` and `mulCtrlDef15_ledger_odd`: compute controlled resource counts.
* `clause76_endpoint`: package word identities and resource bounds.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- The odd-parity step list is the compilation of `sourceRealFamily Φ`. -/
theorem def15Steps_odd (Φ : List ℝ) :
    def15Steps Φ .odd = cppCompile (sourceRealFamily Φ) := rfl

/-- The even-parity step list is the compilation of `sourceRealFamily Φ` with forward and
backward data steps interchanged. -/
theorem def15Steps_even (Φ : List ℝ) :
    def15Steps Φ .even = (cppCompile (sourceRealFamily Φ)).map cppSwapData := rfl

/-- For an odd-length angle list, the odd-parity Definition 15 word equals `sourceRealWord`. -/
theorem def15Word_odd (Φ : List ℝ) {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (hodd : Φ.length % 2 = 1) :
    def15Word U P Q Φ .odd = sourceRealWord U P Q Φ := by
  show cppEvaluate U P Q (def15Steps Φ .odd) = sourceRealWord U P Q Φ
  rw [def15Steps_odd]
  show cppEvaluate U P Q (cppCompile (sourceRealFamily Φ)) = sourceRealWord U P Q Φ
  unfold sourceRealWord
  rw [if_pos hodd]

/-- For an even-length angle list, the even-parity Definition 15 word equals `sourceRealWord`. -/
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

/-- Selecting the parity tag from the angle-list length makes the Definition 15 word equal to
`sourceRealWord`. -/
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

/-- For a phase family of length `d`, compilation has `(d + 1) / 2` forward queries, `d / 2`
adjoint queries, the stated doubled half-length projector counts, and `d` phase macros. -/
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

/-- The odd-parity word has the displayed forward, adjoint, projector-NOT, and phase-macro
counts determined by the angle-list length. -/
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

/-- The even-parity word has the displayed resource ledger, with forward and adjoint query
counts interchanged relative to the odd-parity word. -/
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

/-- The even- and odd-parity words satisfy their respective exact resource ledgers. -/
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

/-- The doubled integer half-lengths have the stated even and odd endpoint values, and their sum
is `2 * d`. -/
theorem def15_parity_endpoints (d : ℕ) :
    (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
    (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
    (2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; omega
  · intro h; omega
  · omega

/-- The five components of the odd-parity resource ledger equal the stated half-length query
counts, doubled projector counts, and phase-list length. -/
theorem def15_ledger_components (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).forwardQueries = (Φ.length + 1) / 2 ∧
    (def15Ledger (def15Steps Φ .odd)).adjointQueries = Φ.length / 2 ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).phaseMacros = Φ.length := by
  rw [def15_ledger]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The five components of the even-parity resource ledger equal the stated half-length query
counts, doubled projector counts, and phase-list length. -/
theorem def15_ledger_components_even (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .even)).forwardQueries = Φ.length / 2 ∧
    (def15Ledger (def15Steps Φ .even)).adjointQueries = (Φ.length + 1) / 2 ∧
    (def15Ledger (def15Steps Φ .even)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .even)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (def15Ledger (def15Steps Φ .even)).phaseMacros = Φ.length := by
  rw [def15_ledger_even]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The odd-parity word has the stated separate projector-NOT counts, with the first count equal
to the length or length minus one according to parity. -/
theorem def15_projectorNot_classes (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).projectorNotP = 2 * (Φ.length / 2) ∧
    (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * ((Φ.length + 1) / 2) ∧
    (Φ.length % 2 = 0 → 2 * (Φ.length / 2) = Φ.length) ∧
    (Φ.length % 2 = 1 → 2 * (Φ.length / 2) = Φ.length - 1) := by
  obtain ⟨_, _, hP, hQ, _⟩ := def15_ledger_components Φ
  refine ⟨hP, hQ, ?_, ?_⟩
  · intro hpar; omega
  · intro hpar; omega

/-- The two projector-NOT counts of the odd-parity word sum to twice the angle-list length. -/
theorem def15_projectorNot_total (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).projectorNotP +
        (def15Ledger (def15Steps Φ .odd)).projectorNotQ = 2 * Φ.length := by
  obtain ⟨_, _, hP, hQ, _⟩ := def15_ledger_components Φ
  omega

/-- The forward and adjoint query counts of the odd-parity word sum to the angle-list length. -/
theorem def15_dataQueries (Φ : List ℝ) :
    (def15Ledger (def15Steps Φ .odd)).forwardQueries +
        (def15Ledger (def15Steps Φ .odd)).adjointQueries = Φ.length := by
  obtain ⟨hF, hA, _, _, _⟩ := def15_ledger_components Φ
  omega

/-- Compilation with controlled phases has the displayed half-length forward and adjoint counts,
twice as many projector-NOT steps as phases, and one controlled phase per family element,
with all other phase and controlled query counts zero. -/
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

/-- Compilation with multiply controlled phases has the displayed half-length data-query counts,
two projector-NOT steps per phase, and one multiply controlled phase per family element,
with the other listed controlled counts zero. -/
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

/-- The odd-parity controlled word has the displayed resource ledger with one controlled phase
per angle and no controlled data or adjoint queries. -/
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

/-- The even-parity controlled word has the displayed resource ledger with reversed forward and
adjoint counts, one controlled phase per angle, and no controlled data or adjoint queries. -/
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

/-- The odd-parity multiply controlled word of length parameter `d` has the displayed ledger,
including `d` multiply controlled phases and zero controlled data and adjoint queries. -/
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

/-- The even-parity multiply controlled word of length parameter `d` has the displayed ledger
with interchanged forward and adjoint counts and `d` multiply controlled phases. -/
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

/-- The odd-parity controlled word has the stated forward, adjoint, projector-NOT, and
controlled-phase counts, and its controlled data-query count is zero. -/
theorem ctrlDef15_ledger_components_odd (Φ : List ℝ) :
    (ctrlCounts (ctrlDef15Steps Φ .odd)).dataQueries = (Φ.length + 1) / 2 ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).adjointQueries = Φ.length / 2 ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).projectorNots =
      2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2) ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledPhaseGates = Φ.length ∧
    (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledDataQueries = 0 := by
  rw [ctrlDef15_ledger_odd]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The odd-parity multiply controlled word has the stated forward, adjoint, projector-NOT, and
multiply controlled phase counts, and its controlled data-query count is zero. -/
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

/-- The parity-dependent Definition 15 words agree with the source words and satisfy the
ordinary, controlled, and multiply controlled resource ledgers together with the stated
parity endpoint identities. See [GilyenSuLowWiebe2019]. -/
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
