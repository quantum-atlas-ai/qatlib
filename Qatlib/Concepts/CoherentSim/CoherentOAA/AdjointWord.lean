/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit

/-!
# Adjoint words for oracle circuits

This module constructs the formal adjoint of an oracle circuit by reversing its instruction
order, taking the adjoint of each fixed gate, and exchanging forward and backward queries. This
is the circuit inverse operation used in amplitude amplification [BrassardEtAl2002].

The evaluation identities relate word concatenation and formal adjoints to matrix multiplication
and conjugate transpose, while the counting identities show that formal adjoints preserve
resource counts.

## Main statements

* `evaluate_append`: concatenation evaluates to the product of the two evaluations.
* `evaluate_adjointCircuit`: the formal adjoint evaluates to the conjugate transpose.
* `adjointQueryCount_adjointCircuit`: the adjoint preserves the query count.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix

section AdjointCircuit
variable {H : Type*}

/-- The adjoint instruction, obtained by taking a gate's conjugate transpose or exchanging
forward and backward oracle queries. -/
noncomputable def adjointInstruction : AdjointStep H → AdjointStep H
  | .gate V => .gate Vᴴ
  | .forward => .backward
  | .backward => .forward

/-- The circuit word obtained by reversing the instruction order and taking every instruction's
adjoint. -/
noncomputable def adjointCircuit : List (AdjointStep H) → List (AdjointStep H)
  | [] => []
  | c :: cs => adjointCircuit cs ++ [adjointInstruction c]

/-- The oracle query count of a concatenation is the sum of the two query counts. -/
@[simp] theorem adjointQueryCount_append (cs ds : List (AdjointStep H)) :
    adjointQueryCount (cs ++ ds) = adjointQueryCount cs + adjointQueryCount ds := by
  induction cs with
  | nil => simp [adjointQueryCount]
  | cons c cs ih => cases c <;> simp [adjointQueryCount, ih, Nat.add_assoc, Nat.add_comm 1]

/-- The fixed gate count of a concatenation is the sum of the two gate counts. -/
@[simp] theorem adjointGateCount_append (cs ds : List (AdjointStep H)) :
    adjointGateCount (cs ++ ds) = adjointGateCount cs + adjointGateCount ds := by
  induction cs with
  | nil => simp [adjointGateCount]
  | cons c cs ih => cases c <;> simp [adjointGateCount, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Taking a circuit's formal adjoint preserves its oracle query count. -/
@[simp] theorem adjointQueryCount_adjointCircuit (cs : List (AdjointStep H)) :
    adjointQueryCount (adjointCircuit cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [adjointCircuit, adjointInstruction, adjointQueryCount, ih]

/-- Taking a circuit's formal adjoint preserves its fixed gate count. -/
@[simp] theorem adjointGateCount_adjointCircuit (cs : List (AdjointStep H)) :
    adjointGateCount (adjointCircuit cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [adjointCircuit, adjointInstruction, adjointGateCount, ih]

variable [Fintype H] [DecidableEq H]

/-- The evaluation of a concatenated circuit word is the product of the two evaluations in list
order. -/
theorem evaluate_append (U : Matrix H H ℂ) (cs ds : List (AdjointStep H)) :
    evaluate U (cs ++ ds) = evaluate U cs * evaluate U ds := by
  induction cs with
  | nil => simp [evaluate]
  | cons c cs ih => simp [evaluate, ih, Matrix.mul_assoc]

/-- Evaluating the formal adjoint word gives the conjugate transpose of the original evaluation. -/
theorem evaluate_adjointCircuit (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate U (adjointCircuit cs) = (evaluate U cs)ᴴ := by
  induction cs with
  | nil => simp [adjointCircuit, evaluate]
  | cons c cs ih =>
    cases c <;> simp [adjointCircuit, evaluate_append, evaluate, instructionMatrix,
      adjointInstruction, ih]
end AdjointCircuit

end Qatlib.Concepts.CoherentSim.CoherentOAA
