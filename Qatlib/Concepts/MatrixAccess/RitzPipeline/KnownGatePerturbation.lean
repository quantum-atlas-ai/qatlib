/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.KnownGateApproximationData
import Qatlib.Concepts.OperatorErrors.Robustness
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

@[simp] theorem replaceKnownGates_queryCount {H : Type*}
    (f : Matrix H H ℂ → Matrix H H ℂ) (cs : List (AdjointStep H)) :
    adjointQueryCount (replaceKnownGates f cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp_all [replaceKnownGates, replaceKnownInstruction, adjointQueryCount]

@[simp] theorem replaceKnownGates_gateCount {H : Type*}
    (f : Matrix H H ℂ → Matrix H H ℂ) (cs : List (AdjointStep H)) :
    adjointGateCount (replaceKnownGates f cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp_all [replaceKnownGates, replaceKnownInstruction, adjointGateCount]

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem replaceKnownGates_wellFormed (cs : List (AdjointStep H))
    (f : Matrix H H ℂ → Matrix H H ℂ) (η : ℝ) (hf : KnownGateApproximation cs f η) :
    WellFormedAdjointCircuit (replaceKnownGates f cs) := by
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    have ht : KnownGateApproximation cs f η :=
      fun A hA => hf A (List.mem_cons_of_mem c hA)
    have hi := ih ht
    cases c with
    | gate A =>
      simpa only [replaceKnownGates, List.map_cons, replaceKnownInstruction,
        WellFormedAdjointCircuit.gate_cons_iff] using And.intro (hf A (by simp)).1 hi
    | forward =>
      simpa only [replaceKnownGates, List.map_cons, replaceKnownInstruction,
        WellFormedAdjointCircuit.forward_cons_iff] using hi
    | backward =>
      simpa only [replaceKnownGates, List.map_cons, replaceKnownInstruction,
        WellFormedAdjointCircuit.backward_cons_iff] using hi

theorem evaluate_known_gate_error (cs : List (AdjointStep H))
    (f : Matrix H H ℂ → Matrix H H ℂ) (η : ℝ) (U : Matrix H H ℂ)
    (hcs : WellFormedAdjointCircuit cs) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hf : KnownGateApproximation cs f η) :
    ‖evaluate U (replaceKnownGates f cs) - evaluate U cs‖ ≤ (adjointGateCount cs : ℝ)*η := by
  induction cs with
  | nil => simp [replaceKnownGates, evaluate, adjointGateCount]
  | cons c cs ih =>
    have ht := ((WellFormedAdjointCircuit.cons_iff c cs).1 hcs).2
    have hft : KnownGateApproximation cs f η :=
      fun A hA => hf A (List.mem_cons_of_mem c hA)
    have hi := ih ht hft
    have hn := unitary_norm_le_one (ht.evaluate_unitary hU)
    cases c with
    | gate A =>
      obtain ⟨hA,he⟩ := hf A (by simp)
      have hh := contractive_product_error (f A) (evaluate U (replaceKnownGates f cs))
        A (evaluate U cs) (unitary_norm_le_one hA) hn
      calc
        _ ≤ ‖evaluate U (replaceKnownGates f cs) - evaluate U cs‖ + ‖f A - A‖ := hh
        _ ≤ (adjointGateCount cs : ℝ)*η + η := add_le_add hi he
        _ = (adjointGateCount (.gate A :: cs) : ℝ)*η := by
          simp only [adjointGateCount, Nat.cast_add, Nat.cast_one]
          ring
    | forward =>
      have hh := contractive_product_error U (evaluate U (replaceKnownGates f cs))
        U (evaluate U cs) (unitary_norm_le_one hU) hn
      simpa only [replaceKnownGates, List.map_cons, replaceKnownInstruction, evaluate,
        instructionMatrix, adjointGateCount, sub_self, norm_zero, add_zero] using hh.trans
          (by simpa using hi)
    | backward =>
      have hh := contractive_product_error Uᴴ (evaluate U (replaceKnownGates f cs))
        Uᴴ (evaluate U cs) (unitary_norm_le_one (adjoint_unitary hU)) hn
      simpa only [replaceKnownGates, List.map_cons, replaceKnownInstruction, evaluate,
        instructionMatrix, adjointGateCount, sub_self, norm_zero, add_zero] using hh.trans
          (by simpa using hi)

theorem known_gate_block_encoding {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (cs : List (AdjointStep H))
    (f : Matrix H H ℂ → Matrix H H ℂ) (η : ℝ) (U : Matrix H H ℂ)
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {A : Matrix O I ℂ}
    (hcs : WellFormedAdjointCircuit cs) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hf : KnownGateApproximation cs f η) (hη : 0 ≤ η)
    (he : ProjectedUnitaryEncoding A (evaluate U cs) L R) :
    BlockEncoding A (evaluate U (replaceKnownGates f cs)) L R 1
      ((adjointGateCount cs : ℝ)*η) := by
  have hw := replaceKnownGates_wellFormed cs f η hf
  refine ⟨hw.evaluate_unitary hU,he.left_isometry,he.right_isometry,
    by norm_num,by positivity,?_⟩
  rw [one_smul, ← he.encoded, norm_sub_rev]
  exact (compress_sub_norm_le he.left_isometry he.right_isometry _ _).trans
    (evaluate_known_gate_error cs f η U hcs hU hf)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
