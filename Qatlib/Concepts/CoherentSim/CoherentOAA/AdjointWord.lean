/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
set_option warningAsError false

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix

section AdjointCircuit
variable {H : Type*}

noncomputable def adjointInstruction : AdjointStep H → AdjointStep H
  | .gate V => .gate Vᴴ
  | .forward => .backward
  | .backward => .forward

noncomputable def adjointCircuit : List (AdjointStep H) → List (AdjointStep H)
  | [] => []
  | c :: cs => adjointCircuit cs ++ [adjointInstruction c]

@[simp] theorem adjointQueryCount_append (cs ds : List (AdjointStep H)) :
    adjointQueryCount (cs ++ ds) = adjointQueryCount cs + adjointQueryCount ds := by
  induction cs with
  | nil => simp [adjointQueryCount]
  | cons c cs ih => cases c <;> simp [adjointQueryCount, ih, Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem adjointGateCount_append (cs ds : List (AdjointStep H)) :
    adjointGateCount (cs ++ ds) = adjointGateCount cs + adjointGateCount ds := by
  induction cs with
  | nil => simp [adjointGateCount]
  | cons c cs ih => cases c <;> simp [adjointGateCount, ih, Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem adjointQueryCount_adjointCircuit (cs : List (AdjointStep H)) :
    adjointQueryCount (adjointCircuit cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [adjointCircuit, adjointInstruction, adjointQueryCount, ih]

@[simp] theorem adjointGateCount_adjointCircuit (cs : List (AdjointStep H)) :
    adjointGateCount (adjointCircuit cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [adjointCircuit, adjointInstruction, adjointGateCount, ih]

variable [Fintype H] [DecidableEq H]

theorem evaluate_append (U : Matrix H H ℂ) (cs ds : List (AdjointStep H)) :
    evaluate U (cs ++ ds) = evaluate U cs * evaluate U ds := by
  induction cs with
  | nil => simp [evaluate]
  | cons c cs ih => simp [evaluate, ih, Matrix.mul_assoc]

theorem evaluate_adjointCircuit (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate U (adjointCircuit cs) = (evaluate U cs)ᴴ := by
  induction cs with
  | nil => simp [adjointCircuit, evaluate]
  | cons c cs ih =>
    cases c <;> simp [adjointCircuit, evaluate_append, evaluate, instructionMatrix,
      adjointInstruction, ih]
end AdjointCircuit

end Qatlib.Concepts.CoherentSim.CoherentOAA
