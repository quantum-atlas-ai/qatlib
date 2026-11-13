/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionCircuitLemmas
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionKernel

/-!
# Finite gate realization of lazy matching access

This module verifies legality and execution of the lazy matching setup, update, and check words.
The setup word exactly prepares the two-neighbor row record, the update word computes the
neighbor register, and the check word writes marked membership into a flag.

The theorem `hasPaidWalkAccess_lazy` packages these constructions as `HasPaidWalkAccess` for
every positive register width, using the identity encoding and a constant setup cost function.
These results concern the quantum walk framework of [Szegedy2004].

## Main statements

* `setup_run`: Exact row record preparation by the finite setup word.
* `check_run`: Exact marked membership flag computation.
* `hasPaidWalkAccess_lazy`: The full paid access specification for lazy matching.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open scoped Classical BigOperators

universe u v

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- For positive register width, the lazy setup word is legal on the doubled workspace. -/
lemma lazySetupWord_legal {m : ℕ} (hm : 1 ≤ m) : finiteWordLegal (m + m) (lazySetupWord m) = true := by
  rw [finiteWordLegal, lazySetupWord, List.all_append, List.all_map]
  simp only [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro p hp
    have hb := highCnotPairs_bound hp
    simp [finiteCodeLegal, hb.1, hb.2.1, hb.2.2]
  · simp [finiteCodeLegal, show m + m - 1 < m + m by omega]

/-- For positive register width, the lazy update word is legal on the doubled workspace. -/
lemma lazyUpdateWord_legal {m : ℕ} (hm : 1 ≤ m) : finiteWordLegal (m + m) (lazyUpdateWord m) = true := by
  rw [finiteWordLegal, lazyUpdateWord, List.all_map, List.all_eq_true]
  intro p hp
  have hb := highCnotPairs_bound hp
  simp [finiteCodeLegal, hb.1, hb.2.1, hb.2.2]

/-- For positive register width, the lazy check word is legal on the doubled workspace. -/
lemma lazyCheckWord_legal {m : ℕ} (hm : 1 ≤ m) : finiteWordLegal (m + m) (lazyCheckWord m) = true := by
  rw [finiteWordLegal, lazyCheckWord, List.all_eq_true]
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  simp [finiteCodeLegal, show m - 1 < m + m by omega, show m < m + m by omega,
    show m - 1 ≠ m by omega]

/-- A function updated at `w` takes the assigned value at `w`. -/
lemma functionUpdate_same {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a)
    (w : α) (v : β w) : Function.update f w v w = v := by
  rw [Function.update]
  rw [dif_pos rfl]

/-- Updating a function at `w` leaves its value unchanged at any different argument. -/
lemma functionUpdate_noteq {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a)
    (w j : α) (v : β w) (h : j ≠ w) : Function.update f w v j = f j := by
  rw [Function.update]
  rw [dif_neg h]

/-- Replacing the final workspace bit of a lazy row record by `b` yields the vertex concatenated
with `lazyRowBasis x b`. -/
lemma lazyRowRecord_update {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (w : Fin (m + m))
    (hw : w.val = m + m - 1) (b : Bool) :
    Function.update (lazyRowRecord m x) w b = regCat x (lazyRowBasis x b) := by
  funext j
  by_cases hj : j = w
  · rw [hj]
    rw [functionUpdate_same]
    have hjval' : j.val = w.val := congrArg Fin.val hj
    have hjtop : j.val = m + m - 1 := by omega
    have hjm : m ≤ j.val := by omega
    have hwm : m ≤ w.val := by omega
    have hjle : w.val - m = m - 1 := by
      have hmm : m + m - 1 = m + (m - 1) := by omega
      rw [hw, hmm]
      omega
    rw [regCat_apply_right _ _ w hwm]
    simp only [lazyRowBasis]
    rw [if_pos (by omega)]
  · by_cases h1 : j.val < m
    · rw [functionUpdate_noteq _ _ _ _ hj]
      rw [lazyRowRecord_apply_vertex x j h1, regCat_apply_left _ _ j h1]
    · by_cases h2 : j.val = m + m - 1
      · have hj1 : j = w := Fin.ext (by omega)
        exact absurd hj1 hj
      · rw [functionUpdate_noteq _ _ _ _ hj]
        rw [lazyRowRecord_apply_agreement hm x j (by omega) h2, regCat_apply_right _ _ j (by omega)]
        simp only [lazyRowBasis]
        rw [if_neg (by omega : ¬ (j.val - m) + 1 = m)]

/-- Applying a Hadamard gate to the final bit of a lazy row record produces the equal-amplitude
superposition of its two neighbor records. -/
lemma setup_applyGate {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (w : Fin (m + m)) (hw : w.val = m + m - 1) :
    ApplyGate (wireGate (m + m) w Hadamard) (Qatlib.Foundations.PureStateMath.Ket (lazyRowRecord m x))
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (regCat x (lazyRowBasis x false))
        + ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (regCat x (lazyRowBasis x true)) := by
  rw [applyGate_wireGate_ket]
  have htop : lazyRowRecord m x w = false := lazyRowRecord_apply_top hm x w hw
  rw [htop]
  simp [Hadamard]
  rw [lazyRowRecord_update hm x w hw false, lazyRowRecord_update hm x w hw true]

/-- The lazy setup word executes on a padded vertex basis state and returns exactly the lazy
matching row record state. -/
lemma setup_run {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    finiteWordRun (m + m) (lazySetupWord m) (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) m x))
      = some (rowBasisRecordState (lazyMatchingKernel m) m (m + m) (fun y => y) x) := by
  rw [finiteWordRun_of_legal (lazySetupWord_legal hm)]
  have hcirc : finiteCodeCircuit (m + m) (lazySetupWord m)
      = (highCnotPairs m).map (fun p => Step.gate (finiteCodeMatrix (m + m) (.cx p.1.val p.2.val)))
        ++ [Step.gate (finiteCodeMatrix (m + m) (.h (m + m - 1)))] := by
    simp [lazySetupWord, finiteCodeCircuit]
  rw [hcirc, run_append]
  have hblock : Run 1 ((highCnotPairs m).map
        (fun p => Step.gate (finiteCodeMatrix (m + m) (.cx p.1.val p.2.val))))
      (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) m x)) = Qatlib.Foundations.PureStateMath.Ket (lazyRowRecord m x) := by
    rw [run_cnot_block_code (highCnotPairs m) (regPad (m + m) m x)
      (fun p hp => by
        obtain ⟨i, h1, h2⟩ := (mem_highCnotPairs p).mp hp
        intro hh
        exact Fin.ne_of_val_ne (by omega) hh)
      (fun p hp => by
        obtain ⟨i, h1, h2⟩ := (mem_highCnotPairs p).mp hp
        exact ⟨by omega, by omega⟩)]
    rfl
  rw [hblock, run_gate]
  rw [finiteCodeMatrix_h (m + m) (m + m - 1) (by omega)]
  rw [setup_applyGate hm x ⟨m + m - 1, by omega⟩ rfl]
  rw [rowBasisRecordState_lazy hm x]
  rw [← cast_sqrt_half]
  rw [run_nil]

/-- The lazy update word sends a vertex and base index basis register to the vertex and its
corresponding neighbor basis register. -/
lemma update_run {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (j : ℕ) :
    finiteWordRun (m + m) (lazyUpdateWord m)
        (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + m) (regCat x (lazyMatchingIndexNat j)))) =
      some (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + m) (regCat x (lazyMatchingNeighbourNat x j)))) := by
  rw [finiteWordRun_of_legal (lazyUpdateWord_legal hm)]
  have hcirc : finiteCodeCircuit (m + m) (lazyUpdateWord m)
      = (highCnotPairs m).map
          (fun p => Step.gate (finiteCodeMatrix (m + m) (.cx p.1.val p.2.val))) := by
    simp [lazyUpdateWord, finiteCodeCircuit]
  rw [hcirc]
  have hblock : Run 1 ((highCnotPairs m).map
        (fun p => Step.gate (finiteCodeMatrix (m + m) (.cx p.1.val p.2.val))))
      (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + m) (regCat x (lazyMatchingIndexNat j)))) =
      Qatlib.Foundations.PureStateMath.Ket (cnotFold (highCnotPairs m) (regPad (m + m) (m + m) (regCat x (lazyMatchingIndexNat j)))) := by
    refine run_cnot_block_code (highCnotPairs m) _ ?_ ?_
    · intro p hp
      obtain ⟨i, h1, h2⟩ := (mem_highCnotPairs p).mp hp
      intro hh
      exact Fin.ne_of_val_ne (by omega) hh
    · intro p hp
      obtain ⟨i, h1, h2⟩ := (mem_highCnotPairs p).mp hp
      exact ⟨by omega, by omega⟩
  rw [hblock, regPad_self, cnotFold_baseRecord hm x j, regPad_self]

/-- A register belongs to the lazy marked set exactly when its top bit is true. -/
lemma mem_lazyMarkedSet_iff {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    (x (lazyTopIndex m hm) = true) ↔ (x ∈ lazyMarkedSet m hm) := by
  rw [lazyMarkedSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- A vertex coordinate of a vertex-plus-flag concatenation equals the corresponding vertex bit. -/
lemma regCat_vertex_value {m : ℕ} (x : Reg m) (s : Reg 1) (i : Fin (m + 1)) (hi : i.val < m) :
    regCat x s i = x ⟨i.val, hi⟩ :=
  regCat_apply_left x s i hi

/-- The last coordinate of a vertex-plus-flag concatenation equals the unique flag bit. -/
lemma regCat_flag_value {m : ℕ} (x : Reg m) (s : Reg 1) (v : ℕ) (hv : v < m + 1) (hi : v = m) :
    regCat x s ⟨v, hv⟩ = s ⟨0, by omega⟩ := by
  have hle : m ≤ v := by omega
  have hval : (⟨v, hv⟩ : Fin (m + 1)).val = v := rfl
  refine regCat_apply_right' x s ⟨v, hv⟩ hle ⟨0, by omega⟩ ?_
  omega

/-- The top bit of the vertex register, used to indicate membership in the lazy marked set. -/
def lazyMarkedBit (m : ℕ) (hm : 1 ≤ m) (x : Reg m) : Bool := x (lazyTopIndex m hm)

/-- The lazy marked bit equals the Boolean decision of membership in the lazy marked set. -/
lemma lazyMarkedBit_eq_decide {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    lazyMarkedBit m hm x = decide (x ∈ lazyMarkedSet m hm) := by
  unfold lazyMarkedBit
  have hiff : (x (lazyTopIndex m hm) = true) ↔ (x ∈ lazyMarkedSet m hm) :=
    mem_lazyMarkedSet_iff hm x
  by_cases hp : x ∈ lazyMarkedSet m hm
  · have ha : x (lazyTopIndex m hm) = true := hiff.mpr hp
    simp [ha, decide_eq_true_eq.mpr hp]
  · have ha : x (lazyTopIndex m hm) ≠ true := fun hcon => hp (hiff.mp hcon)
    have hb : x (lazyTopIndex m hm) = false := Bool.eq_false_of_not_eq_true ha
    have hdec : (decide (x ∈ lazyMarkedSet m hm)) = false := by
      rw [decide_eq_false_iff_not]
      exact hp
    simp [hb, hdec]

/-- Updating the flag wire in the padded vertex and false-flag register yields the padded
register with the assigned flag. -/
lemma regPad_flagged_update {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (f : Bool) :
    Function.update (regPad (m + m) (m + 1) (regCat x (fun _ => false))) (lazyFlagWire m hm) f
      = regPad (m + m) (m + 1) (regCat x (fun _ => f)) := by
  have hconv : (⟨m, by omega⟩ : Fin (m + 1)) = lazyFlagIndex m := rfl
  funext w
  by_cases hw : w.val = m
  · have hw' : w = lazyFlagWire m hm := by
      refine Fin.ext ?_
      rw [lazyFlagWire_val hm]
      exact hw
    rw [hw', functionUpdate_same]
    rw [regPad_apply', lazyFlagWire_val hm, dif_pos (by omega)]
    rw [hconv]
    calc f = (fun _ : Fin 1 => f) ⟨0, by omega⟩ := rfl
      _ = (regCat x (fun _ => f)) (lazyFlagIndex m) := by
        symm
        exact regCat_flag_value x (fun _ => f) m (by omega) rfl
  · have hw' : w ≠ lazyFlagWire m hm := by
      intro hh
      have hval := congrArg Fin.val hh
      rw [lazyFlagWire_val hm] at hval
      omega
    rw [functionUpdate_noteq _ _ _ _ hw']
    rw [regPad_apply', regPad_apply']
    by_cases h1 : w.val < m + 1
    · rw [dif_pos h1, dif_pos h1]
      by_cases h2 : w.val < m
      · rw [regCat_vertex_value x (fun _ => f) ⟨w.val, h1⟩ h2,
          regCat_vertex_value x (fun _ => false) ⟨w.val, h1⟩ h2]
      · exfalso
        omega
    · rw [dif_neg h1, dif_neg h1]

/-- The XOR of the false flag wire and the control wire in the initial padded register equals
the marked membership bit. -/
lemma check_flag_value {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    Bool.xor ((regPad (m + m) (m + 1) (regCat x (fun _ => false))) (lazyFlagWire m hm))
      ((regPad (m + m) (m + 1) (regCat x (fun _ => false))) (lazyCtlWire m hm))
      = decide (x ∈ lazyMarkedSet m hm) := by
  have hci : (lazyCtlIndex m hm).val = m - 1 := lazyCtlIndex_val hm
  have hflag : (regPad (m + m) (m + 1) (regCat x (fun _ => false))) (lazyFlagWire m hm) = false := by
    rw [regPad_apply', lazyFlagWire_val hm, dif_pos (by omega)]
    have hconv : (⟨m, by omega⟩ : Fin (m + 1)) = lazyFlagIndex m := rfl
    rw [hconv]
    calc (regCat x (fun _ => false)) (lazyFlagIndex m)
        = (fun _ : Fin 1 => false) ⟨0, by omega⟩ := by
          rw [show lazyFlagIndex m = ⟨m, by omega⟩ from rfl]
          exact regCat_flag_value x (fun _ => false) m (by omega) rfl
      _ = false := rfl
  have hctl : (regPad (m + m) (m + 1) (regCat x (fun _ => false))) (lazyCtlWire m hm)
      = lazyMarkedBit m hm x := by
    rw [regPad_apply', lazyCtlWire_val hm, dif_pos (by omega)]
    have hconv : (⟨m - 1, by omega⟩ : Fin (m + 1)) = lazyCtlIndex m hm := rfl
    rw [hconv]
    rw [regCat_vertex_value x (fun _ => false) (lazyCtlIndex m hm) (by omega)]
    unfold lazyMarkedBit
    congr 1
  rw [hflag, hctl]
  simp [lazyMarkedBit_eq_decide hm x]

/-- The lazy check word preserves the vertex and writes its marked membership into the initially
false flag. -/
lemma check_run {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    finiteWordRun (m + m) (lazyCheckWord m)
        (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + 1) (regCat x (fun _ => false)))) =
      some (Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + 1) (regCat x (fun _ => decide (x ∈ lazyMarkedSet m hm))))) := by
  rw [finiteWordRun_of_legal (lazyCheckWord_legal hm)]
  have hcirc : finiteCodeCircuit (m + m) (lazyCheckWord m)
      = [Step.gate (finiteCodeMatrix (m + m) (.cx (m - 1) m))] := by
    simp [lazyCheckWord, finiteCodeCircuit]
  rw [hcirc, run_gate]
  rw [finiteCodeMatrix_cx (m + m) (m - 1) m (⟨by omega, by omega, by omega⟩)]
  have hne : (⟨m - 1, by omega⟩ : Fin (m + m)) ≠ (⟨m, by omega⟩ : Fin (m + m)) := by
    intro hh
    have hval : m - 1 = m := congrArg Fin.val hh
    omega
  rw [applyGate_cnotGate_ket (m + m) ⟨m - 1, by omega⟩ ⟨m, by omega⟩ hne]
  have hctl_eq : (⟨m - 1, by omega⟩ : Fin (m + m)) = lazyCtlWire m hm := by
    refine Fin.ext ?_
    rw [lazyCtlWire_val hm]
  have hflag_eq : (⟨m, by omega⟩ : Fin (m + m)) = lazyFlagWire m hm := by
    refine Fin.ext ?_
    rw [lazyFlagWire_val hm]
  rw [hctl_eq, hflag_eq]
  rw [check_flag_value hm x, regPad_flagged_update hm x, run_nil]

/-- For positive register width, the lazy matching kernel and marked set possess paid walk
access using the specified setup, update, and check words, identity encoding, and constant
setup cost. -/
theorem hasPaidWalkAccess_lazy {m : ℕ} (hm : 1 ≤ m) :
    HasPaidWalkAccess (P := lazyMatchingKernel m) (S := lazyMarkedSet m hm)
      (a := m) (w := m + m) (enc := fun x => x)
      (support := lazySupport) (idx := lazyMatchingIndexNat) (nbr := lazyMatchingNeighbourNat)
      (setupWord := lazySetupWord m) (updateWord := lazyUpdateWord m)
      (checkWord := lazyCheckWord m) (C := fun _ => (lazySetupWord m).length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Function.injective_id
  · exact lazySetupWord_legal hm
  · exact lazyUpdateWord_legal hm
  · exact lazyCheckWord_legal hm
  · intro x eps heps
    refine ⟨rowBasisRecordState (lazyMatchingKernel m) m (m + m) (fun y => y) x, ?_, ?_, ?_⟩
    · exact setup_run hm x
    · have hz : (∑ i, ‖(rowBasisRecordState (lazyMatchingKernel m) m (m + m)
          (fun y => y) x i - rowBasisRecordState (lazyMatchingKernel m) m (m + m)
          (fun y => y) x i)‖ ^ 2) = 0 := by
        simp
      rw [hz]
      positivity
    · exact le_refl _
  · intro x j hj
    exact update_run hm x j
  · intro x
    exact check_run hm x
  · have hl := lazy_word_lengths m
    rw [hl.2.1]
    simp [highCnotPairs]
    omega
  · have hl := lazy_word_lengths m
    rw [hl.2.2]
    omega
  · omega
  · intro j
    exact ⟨rfl, rfl⟩
end Qatlib.Concepts.WalkSearch.FrameSpectral
