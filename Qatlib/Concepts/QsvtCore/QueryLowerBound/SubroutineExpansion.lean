/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.AdjointCircuits
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QsvtCore.QueryLowerBound

open Matrix

variable {H : Type}

noncomputable def substituteAdjointCircuit [Fintype H] [DecidableEq H]
    (body cs : List (AdjointStep H)) : List (AdjointStep H) :=
  cs.flatMap fun
    | .gate V => [.gate V]
    | .forward => body
    | .backward => Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit body

def repeatAdjointWord (cs : List (AdjointStep H)) (n : ℕ) : List (AdjointStep H) :=
  (List.replicate n cs).flatten

theorem substituteAdjointCircuit_cons [Fintype H] [DecidableEq H]
    (body : List (AdjointStep H)) (c : AdjointStep H) (cs : List (AdjointStep H)) :
    substituteAdjointCircuit body (c :: cs) =
      (match c with
        | .gate V => [.gate V]
        | .forward => body
        | .backward => Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit body) ++ substituteAdjointCircuit body cs :=
  rfl

theorem substitute_adjoint_syntax_laws [Fintype H] [DecidableEq H]
    (body cs ds : List (AdjointStep H)) :
    substituteAdjointCircuit body (cs ++ ds) =
        substituteAdjointCircuit body cs ++ substituteAdjointCircuit body ds ∧
      substituteAdjointCircuit body (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body cs) := by
  refine ⟨List.flatMap_append, ?_⟩
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hstep : substituteAdjointCircuit body [adjointInstruction c] =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body [c]) := by
      cases c <;> simp [substituteAdjointCircuit, adjointInstruction,
          Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit]
    calc substituteAdjointCircuit body (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (c :: cs))
        = substituteAdjointCircuit body (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) ++
            substituteAdjointCircuit body [adjointInstruction c] := by
          rw [show Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (c :: cs) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs ++ [adjointInstruction c]
            from by simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit]]
          exact List.flatMap_append
      _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body cs) ++
            Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body [c]) := by rw [ih, hstep]
      _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body [c] ++
            substituteAdjointCircuit body cs) := by rw [adjointCircuit_append]
      _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (substituteAdjointCircuit body (c :: cs)) := by
          congr 1
          exact List.flatMap_append.symm

theorem substitute_adjoint_evaluate_cost [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (body cs : List (AdjointStep H)) :
    evaluate O (substituteAdjointCircuit body cs) = evaluate (evaluate O body) cs ∧
      adjointQueryCount (substituteAdjointCircuit body cs) =
        adjointQueryCount cs * adjointQueryCount body ∧
      adjointGateCount (substituteAdjointCircuit body cs) =
        adjointGateCount cs + adjointQueryCount cs * adjointGateCount body ∧
      (WellFormedAdjointCircuit body → WellFormedAdjointCircuit cs →
        WellFormedAdjointCircuit (substituteAdjointCircuit body cs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction cs with
    | nil => rfl
    | cons c cs ih =>
      rw [substituteAdjointCircuit_cons, evaluate_append, ih]
      cases c <;> simp [evaluate, instructionMatrix, evaluate_adjointCircuit]
  · induction cs with
    | nil => simp [substituteAdjointCircuit, adjointQueryCount]
    | cons c cs ih =>
      rw [substituteAdjointCircuit_cons, adjointQueryCount_append, ih]
      cases c <;> simp [adjointQueryCount, adjointQueryCount_adjointCircuit] <;> ring
  · induction cs with
    | nil => simp [substituteAdjointCircuit, adjointQueryCount, adjointGateCount]
    | cons c cs ih =>
      rw [substituteAdjointCircuit_cons, adjointGateCount_append, ih]
      cases c <;> simp [adjointQueryCount, adjointGateCount,
        adjointGateCount_adjointCircuit] <;> ring
  · intro hbody hcs V hV
    obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp hV
    cases c with
    | gate W =>
      have hVW : V = W := by simpa using hmem
      rw [hVW]
      exact hcs _ hc
    | forward => exact hbody _ hmem
    | backward => exact hbody.adjointCircuit _ hmem

theorem repeat_adjoint_word_semantics_cost [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (cs : List (AdjointStep H)) (n : ℕ) :
    evaluate O (repeatAdjointWord cs n) = (evaluate O cs) ^ n ∧
      adjointQueryCount (repeatAdjointWord cs n) = n * adjointQueryCount cs ∧
      adjointGateCount (repeatAdjointWord cs n) = n * adjointGateCount cs ∧
      (WellFormedAdjointCircuit cs → WellFormedAdjointCircuit (repeatAdjointWord cs n)) := by
  induction n with
  | zero => exact ⟨rfl, by simp [repeatAdjointWord, adjointQueryCount], by simp [repeatAdjointWord, adjointGateCount],
      fun _ => WellFormedAdjointCircuit.nil⟩
  | succ n ih =>
    have hrep : repeatAdjointWord cs (n + 1) = cs ++ repeatAdjointWord cs n := by
      simp [repeatAdjointWord, List.replicate_succ]
    obtain ⟨ihe, ihq, ihg, ihw⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrep, evaluate_append, ihe, pow_succ']
    · rw [hrep, adjointQueryCount_append, ihq]
      ring
    · rw [hrep, adjointGateCount_append, ihg]
      ring
    · intro hcs
      rw [hrep]
      exact hcs.append (ihw hcs)

end Qatlib.Concepts.QsvtCore.QueryLowerBound
