/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.QuerySpaceReference

/-!
# Bit queries from a known phase reference

This module defines a correction gate and a one-query circuit that implements workspace
bit access using a bare phase oracle and a reference index of known Boolean value.
The construction is a phase-kickback conversion of the kind described in [NielsenChuang2010].

`knownOneBitCircuit` uses one oracle query and five gates. Its correctness theorem
preserves the reference input while applying the workspace bit oracle to the data.

## Main statements

* `corrected_routed_bare_reference`: the correction yields the desired workspace phase action.
* `knownOneBitCircuit_gates`: the simulation uses five gates.
* `run_knownOneBitCircuit`: the simulation realizes a workspace bit query.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.CompressedQuery.CompressOracle

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib Matrix
open scoped Classical BigOperators

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The diagonal phase correction determined by the known Boolean reference value and the data
response bit. -/
def knownCorrection (c : Bool) : Matrix (Full I W) (Full I W) ℂ :=
  PhaseOracle (fun q : Full I W => c && !q.1.1.2)

/-- The known-reference phase correction is unitary. -/
theorem knownCorrection_unitary (c : Bool) :
    knownCorrection (I := I) (W := W) c ∈ unitaryGroup (Full I W) ℂ :=
  phaseOracle_unitary _

omit [Fintype I] [Fintype W] in

/-- For reference value false, the correction matrix is the identity. -/
theorem knownCorrection_false :
    knownCorrection (I := I) (W := W) false = 1 := by
  simp [knownCorrection, PhaseOracle]

/-- Routing a bare phase query through a reference index of value `c` and applying the
correction realizes the workspace phase oracle. -/
theorem corrected_routed_bare_reference (f : I → Bool) (r : I) (c : Bool)
    (hfr : f r = c) (ψ : QState (Data I W)) :
    ApplyGate (knownCorrection c)
      (ApplyGate routeGate (ApplyGate (bareOracle f) (ApplyGate routeGate (referenceInput r ψ)))) =
        referenceInput r (ApplyGate (workspacePhaseOracle f) ψ) := by
  funext q
  rcases q with ⟨⟨⟨x, b⟩, w⟩, s⟩
  rw [knownCorrection, applyGate_phaseOracle, routed_bare_apply]
  change (if c && !b then (-1 : ℂ) else 1) *
      ((if f (route (((x, b), w), s)).2 then (-1 : ℂ) else 1) *
        (ψ ((x, b), w) * Ket r s)) =
    ApplyGate (workspacePhaseOracle f) ψ ((x, b), w) * Ket r s
  rw [workspacePhase_apply]
  by_cases hs : s = r
  · subst s
    cases c <;> cases b <;> simp [route, hfr]
  · simp [Qatlib.Foundations.PureStateMath.Ket, hs]

/-- The known-reference bit-query simulation formed from two data Hadamards, two routing gates,
one correction, and one bare query. -/
def knownOneBitCircuit (c : Bool) : Circuit (Full I W) :=
  [Step.gate dataHadamard, Step.gate routeGate, Step.query, Step.gate routeGate,
    Step.gate (knownCorrection c), Step.gate dataHadamard]

/-- The known-reference bit-query simulation is a unitary circuit. -/
theorem knownOneBitCircuit_unitary (c : Bool) :
    IsUnitaryCircuit (knownOneBitCircuit (I := I) (W := W) c) := by
  simp only [knownOneBitCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query,
      isUnitaryCircuit_nil]
  exact ⟨dataHadamard_unitary, routeGate_unitary, routeGate_unitary,
    knownCorrection_unitary c, dataHadamard_unitary, trivial⟩

omit [Fintype I] [Fintype W] in

/-- The known-reference bit-query simulation uses exactly one oracle query. -/
theorem knownOneBitCircuit_queries (c : Bool) :
    QueryCount (knownOneBitCircuit (I := I) (W := W) c) = 1 := by
  rfl

omit [Fintype I] [Fintype W] in

/-- The known-reference bit-query simulation uses exactly five gates. -/
theorem knownOneBitCircuit_gates (c : Bool) :
    GateCount (knownOneBitCircuit (I := I) (W := W) c) = 5 := by
  rfl

/-- With a reference index whose oracle value is `c`, the circuit applies the workspace bit
oracle while preserving the reference input form. -/
theorem run_knownOneBitCircuit (f : I → Bool) (r : I) (c : Bool) (hfr : f r = c)
    (ψ : QState (Data I W)) :
    Run (bareOracle f) (knownOneBitCircuit c) (referenceInput r ψ) =
      referenceInput r (ApplyGate (workspaceBitOracle f) ψ) := by
  simp only [knownOneBitCircuit, run_gate, run_query, run_nil]
  change ApplyGate (TensorGate controlHadamard (1 : Matrix I I ℂ))
    (ApplyGate (knownCorrection c) (ApplyGate routeGate (ApplyGate (bareOracle f)
      (ApplyGate routeGate (ApplyGate (TensorGate controlHadamard (1 : Matrix I I ℂ))
        (referenceInput r ψ)))))) = _
  rw [lifted_gate_reference, corrected_routed_bare_reference f r c hfr, lifted_gate_reference]
  congr 1
  rw [← applyGate_mul, ← applyGate_mul, controlHadamard_mul_phase_mul_controlHadamard]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
