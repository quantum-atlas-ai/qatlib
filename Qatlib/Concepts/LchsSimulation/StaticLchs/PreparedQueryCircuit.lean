/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib

inductive PreparedStep (H : Type*) where
  | gate : Matrix H H ℂ → PreparedStep H
  | dataForward : PreparedStep H
  | dataBackward : PreparedStep H
  | prepareForward : PreparedStep H
  | prepareBackward : PreparedStep H

noncomputable def preparedOfAdjoint {H : Type*} : AdjointStep H → PreparedStep H
  | .gate V => .gate V
  | .forward => .dataForward
  | .backward => .dataBackward

noncomputable def preparedTrial {H : Type*} (cs : List (AdjointStep H)) : List (PreparedStep H) :=
  cs.map preparedOfAdjoint ++ [.prepareForward]

def preparedDataQueries {H : Type*} : List (PreparedStep H) → ℕ
  | [] => 0
  | .dataForward :: cs => preparedDataQueries cs + 1
  | .dataBackward :: cs => preparedDataQueries cs + 1
  | _ :: cs => preparedDataQueries cs

def preparedInputQueries {H : Type*} : List (PreparedStep H) → ℕ
  | [] => 0
  | .prepareForward :: cs => preparedInputQueries cs + 1
  | .prepareBackward :: cs => preparedInputQueries cs + 1
  | _ :: cs => preparedInputQueries cs

def preparedFixedGates {H : Type*} : List (PreparedStep H) → ℕ
  | [] => 0
  | .gate _ :: cs => preparedFixedGates cs + 1
  | _ :: cs => preparedFixedGates cs

section PreparedSemantics
variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def preparedInstruction (U B : Matrix H H ℂ) : PreparedStep H → Matrix H H ℂ
  | .gate V => V
  | .dataForward => U
  | .dataBackward => Uᴴ
  | .prepareForward => B
  | .prepareBackward => Bᴴ

noncomputable def evaluatePrepared (U B : Matrix H H ℂ) : List (PreparedStep H) → Matrix H H ℂ
  | [] => 1
  | c :: cs => preparedInstruction U B c * evaluatePrepared U B cs

def PreparedInstructionValid : PreparedStep H → Prop
  | .gate V => V ∈ Matrix.unitaryGroup H ℂ
  | _ => True

def PreparedCircuitValid (cs : List (PreparedStep H)) : Prop :=
  ∀ c ∈ cs, PreparedInstructionValid c

theorem preparedInstruction_unitary {U B : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    {c : PreparedStep H} (hc : PreparedInstructionValid c) :
    preparedInstruction U B c ∈ Matrix.unitaryGroup H ℂ := by
  cases c with
  | gate V => exact hc
  | dataForward => exact hU
  | dataBackward => exact adjoint_unitary hU
  | prepareForward => exact hB
  | prepareBackward => exact adjoint_unitary hB

theorem PreparedCircuitValid.evaluate_unitary {cs : List (PreparedStep H)}
    (hcs : PreparedCircuitValid cs) {U B : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ) :
    evaluatePrepared U B cs ∈ Matrix.unitaryGroup H ℂ := by
  induction cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons c cs ih =>
    exact (Matrix.unitaryGroup H ℂ).mul_mem
      (preparedInstruction_unitary hU hB (hcs c (by simp)))
      (ih (fun d hd => hcs d (List.mem_cons_of_mem c hd)))

theorem evaluatePrepared_append (U B : Matrix H H ℂ) (cs ds : List (PreparedStep H)) :
    evaluatePrepared U B (cs ++ ds) = evaluatePrepared U B cs * evaluatePrepared U B ds := by
  induction cs with
  | nil => simp [evaluatePrepared]
  | cons c cs ih => simp [evaluatePrepared, ih, Matrix.mul_assoc]

theorem evaluatePrepared_map (U B : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluatePrepared U B (cs.map preparedOfAdjoint) = evaluate U cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [evaluatePrepared, preparedOfAdjoint, preparedInstruction,
      evaluate, instructionMatrix, ih]

theorem evaluate_preparedTrial (U B : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluatePrepared U B (preparedTrial cs) = evaluate U cs * B := by
  simp [preparedTrial, evaluatePrepared_append, evaluatePrepared_map, evaluatePrepared,
    preparedInstruction]

theorem preparedTrial_valid {cs : List (AdjointStep H)}
    (hcs : ∀ V, AdjointStep.gate V ∈ cs → V ∈ Matrix.unitaryGroup H ℂ) :
    PreparedCircuitValid (preparedTrial cs) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    cases d with
    | gate V => exact hcs V hd
    | forward => trivial
    | backward => trivial
  · have : c = .prepareForward := List.mem_singleton.mp hc
    subst c
    trivial

theorem preparedTrial_apply {I : Type*} [Fintype I] {U B : Matrix H H ℂ}
    (cs : List (AdjointStep H)) (zero : H) (R : Matrix H I ℂ) (b : QState I)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ b) :
    ApplyGate (evaluatePrepared U B (preparedTrial cs)) (Ket zero) =
      ApplyGate (evaluate U cs) (R *ᵥ b) := by
  rw [evaluate_preparedTrial]
  simpa only [ApplyGate, Matrix.mulVec_mulVec] using
    congrArg (ApplyGate (evaluate U cs)) hprepare

end PreparedSemantics

section Counts
variable {H : Type*}

theorem preparedCounts_append (cs ds : List (PreparedStep H)) :
    preparedDataQueries (cs ++ ds) = preparedDataQueries cs + preparedDataQueries ds ∧
    preparedInputQueries (cs ++ ds) = preparedInputQueries cs + preparedInputQueries ds ∧
    preparedFixedGates (cs ++ ds) = preparedFixedGates cs + preparedFixedGates ds := by
  induction cs with
  | nil => simp [preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | cons c cs ih =>
    cases c <;> simp [preparedDataQueries, preparedInputQueries, preparedFixedGates,
      ih.1, ih.2.1, ih.2.2, Nat.add_assoc, Nat.add_comm 1]

theorem preparedTrial_counts (cs : List (AdjointStep H)) :
    preparedDataQueries (preparedTrial cs) = adjointQueryCount cs ∧
    preparedInputQueries (preparedTrial cs) = 1 ∧
    preparedFixedGates (preparedTrial cs) = adjointGateCount cs := by
  have hm : preparedDataQueries (cs.map preparedOfAdjoint) = adjointQueryCount cs ∧
      preparedInputQueries (cs.map preparedOfAdjoint) = 0 ∧
      preparedFixedGates (cs.map preparedOfAdjoint) = adjointGateCount cs := by
    induction cs with
    | nil => trivial
    | cons c cs ih =>
      cases c <;> simp [preparedOfAdjoint, preparedDataQueries, preparedInputQueries,
        preparedFixedGates, adjointQueryCount, adjointGateCount, ih.1, ih.2.1, ih.2.2]
  rcases preparedCounts_append (cs.map preparedOfAdjoint) [.prepareForward] with ⟨hu, hb, hg⟩
  simp only [preparedTrial, hu, hb, hg, hm.1, hm.2.1, hm.2.2,
    preparedDataQueries, preparedInputQueries, preparedFixedGates, Nat.add_zero, Nat.zero_add]
  trivial

end Counts
end Qatlib.Concepts.LchsSimulation.StaticLchs
