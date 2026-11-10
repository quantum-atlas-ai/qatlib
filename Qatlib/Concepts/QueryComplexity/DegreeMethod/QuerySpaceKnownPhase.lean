/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.QuerySpaceReference
set_option warningAsError false
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
set_option linter.unusedSectionVars false

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def knownCorrection (c : Bool) : Matrix (Full I W) (Full I W) ℂ :=
  PhaseOracle (fun q : Full I W => c && !q.1.1.2)

theorem knownCorrection_unitary (c : Bool) :
    knownCorrection (I := I) (W := W) c ∈ unitaryGroup (Full I W) ℂ :=
  phaseOracle_unitary _

theorem knownCorrection_false :
    knownCorrection (I := I) (W := W) false = 1 := by
  simp [knownCorrection, PhaseOracle]

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

def knownOneBitCircuit (c : Bool) : Circuit (Full I W) :=
  [Step.gate dataHadamard, Step.gate routeGate, Step.query, Step.gate routeGate,
    Step.gate (knownCorrection c), Step.gate dataHadamard]

theorem knownOneBitCircuit_unitary (c : Bool) :
    IsUnitaryCircuit (knownOneBitCircuit (I := I) (W := W) c) := by
  simp only [knownOneBitCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query,
      isUnitaryCircuit_nil]
  exact ⟨dataHadamard_unitary, routeGate_unitary, routeGate_unitary,
    knownCorrection_unitary c, dataHadamard_unitary, trivial⟩

theorem knownOneBitCircuit_queries (c : Bool) :
    QueryCount (knownOneBitCircuit (I := I) (W := W) c) = 1 := by
  rfl

theorem knownOneBitCircuit_gates (c : Bool) :
    GateCount (knownOneBitCircuit (I := I) (W := W) c) = 5 := by
  rfl

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
