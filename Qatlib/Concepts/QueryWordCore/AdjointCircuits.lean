/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false

namespace Qatlib.Concepts.QueryWordCore.AdjointCircuits

open Matrix

variable {H : Type*}

@[simp] theorem adjointInstruction_involutive (c : AdjointStep H) :
    adjointInstruction (adjointInstruction c) = c := by
  cases c <;> simp [adjointInstruction]

@[simp] theorem adjointCircuit_append (cs ds : List (AdjointStep H)) :
    adjointCircuit (cs ++ ds) = adjointCircuit ds ++ adjointCircuit cs := by
  induction cs with
  | nil => simp [adjointCircuit]
  | cons c cs ih => simp [adjointCircuit, ih, List.append_assoc]

@[simp] theorem adjointCircuit_involutive (cs : List (AdjointStep H)) :
    adjointCircuit (adjointCircuit cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [adjointCircuit, ih]

variable [Fintype H] [DecidableEq H]

theorem adjointCircuit_roundTrip (U : Matrix H H ℂ) (cs : List (AdjointStep H))
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (cs ++ adjointCircuit cs) ∧
    evaluate U (cs ++ adjointCircuit cs) = 1 ∧
    adjointQueryCount (cs ++ adjointCircuit cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (cs ++ adjointCircuit cs) = 2 * adjointGateCount cs := by
  refine ⟨hcs.append hcs.adjointCircuit, ?_, ?_, ?_⟩
  · rw [evaluate_append, evaluate_adjointCircuit]
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (hcs.evaluate_unitary hU)
  · simp only [adjointQueryCount_append, adjointQueryCount_adjointCircuit, two_mul]
  · simp only [adjointGateCount_append, adjointGateCount_adjointCircuit, two_mul]

theorem adjointCircuit_reverseRoundTrip (U : Matrix H H ℂ) (cs : List (AdjointStep H))
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (adjointCircuit cs ++ cs) ∧
    evaluate U (adjointCircuit cs ++ cs) = 1 ∧
    adjointQueryCount (adjointCircuit cs ++ cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (adjointCircuit cs ++ cs) = 2 * adjointGateCount cs := by
  refine ⟨hcs.adjointCircuit.append hcs, ?_, ?_, ?_⟩
  · rw [evaluate_append, evaluate_adjointCircuit]
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (hcs.evaluate_unitary hU)
  · simp only [adjointQueryCount_append, adjointQueryCount_adjointCircuit, two_mul]
  · simp only [adjointGateCount_append, adjointGateCount_adjointCircuit, two_mul]

end Qatlib.Concepts.QueryWordCore.AdjointCircuits
