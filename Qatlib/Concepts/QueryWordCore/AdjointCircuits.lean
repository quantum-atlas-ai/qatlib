/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

/-!
# Adjoint circuit round trips

This module proves involutivity and concatenation identities for adjoint instructions and
circuits. A well-formed circuit composed with its adjoint in either order evaluates to the
identity and doubles both query and gate counts.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `adjointCircuit_involutive`: taking the circuit adjoint twice restores the circuit.
* `adjointCircuit_roundTrip`: a circuit followed by its adjoint.
* `adjointCircuit_reverseRoundTrip`: the reverse composition.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false

namespace Qatlib.Concepts.QueryWordCore.AdjointCircuits

open Matrix

variable {H : Type*}

/-- Taking the adjoint of an instruction twice returns the original instruction. -/
@[simp] theorem adjointInstruction_involutive (c : AdjointStep H) :
    adjointInstruction (adjointInstruction c) = c := by
  cases c <;> simp [adjointInstruction]

/-- The adjoint of a concatenation is the concatenation of the adjoints in reverse order. -/
@[simp] theorem adjointCircuit_append (cs ds : List (AdjointStep H)) :
    adjointCircuit (cs ++ ds) = adjointCircuit ds ++ adjointCircuit cs := by
  induction cs with
  | nil => simp [adjointCircuit]
  | cons c cs ih => simp [adjointCircuit, ih, List.append_assoc]

/-- Taking the adjoint of a circuit twice returns the original circuit. -/
@[simp] theorem adjointCircuit_involutive (cs : List (AdjointStep H)) :
    adjointCircuit (adjointCircuit cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [adjointCircuit, ih]

variable [Fintype H] [DecidableEq H]

/-- A well-formed circuit followed by its adjoint is well formed, evaluates to the identity for
a unitary oracle, and doubles its query and gate counts. -/
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

/-- The adjoint of a well-formed circuit followed by that circuit is well formed, evaluates to
the identity for a unitary oracle, and doubles its query and gate counts. -/
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
