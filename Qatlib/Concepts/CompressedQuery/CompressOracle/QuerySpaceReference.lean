/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CompressedQuery.CompressOracle

open Qatlib Matrix
open scoped Classical BigOperators
set_option linter.unusedSectionVars false

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

abbrev Data (I W : Type) := (I × Bool) × W
abbrev Full (I W : Type) := Data I W × I

def route : Full I W → Full I W
  | (((x, false), w), r) => (((x, false), w), r)
  | (((x, true), w), r) => (((r, true), w), x)

theorem route_involutive : Function.Involutive (route (I := I) (W := W)) := by
  rintro ⟨⟨⟨x, b⟩, w⟩, r⟩
  cases b <;> rfl

def routeGate : Matrix (Full I W) (Full I W) ℂ := permMatrix route

theorem routeGate_unitary : routeGate (I := I) (W := W) ∈ unitaryGroup (Full I W) ℂ :=
  permMatrix_unitary route_involutive

def bareOracle (f : I → Bool) : Matrix (Full I W) (Full I W) ℂ :=
  TensorGate (1 : Matrix (Data I W) (Data I W) ℂ) (PhaseOracle f)

theorem bareOracle_unitary (f : I → Bool) :
    bareOracle (W := W) f ∈ unitaryGroup (Full I W) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _) (phaseOracle_unitary f)

def referenceInput (r : I) (ψ : QState (Data I W)) : QState (Full I W) :=
  TensorState ψ (Ket r)

theorem bareOracle_apply (f : I → Bool) (v : QState (Full I W))
    (q : Data I W) (r : I) :
    ApplyGate (bareOracle f) v (q, r) = (if f r then (-1 : ℂ) else 1) * v (q, r) := by
  have hslice : ApplyGate (bareOracle f) v (q, r) =
      ApplyGate (PhaseOracle f) (fun x => v (q, x)) r := by
    simp [bareOracle, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.one_apply]
  rw [hslice, applyGate_phaseOracle]

theorem routed_bare_apply (f : I → Bool) (v : QState (Full I W)) (q : Full I W) :
    ApplyGate routeGate (ApplyGate (bareOracle f) (ApplyGate routeGate v)) q =
      (if f (route q).2 then (-1 : ℂ) else 1) * v q := by
  change ApplyGate (permMatrix route) (ApplyGate (bareOracle f)
    (ApplyGate (permMatrix route) v)) q = _
  rw [applyGate_permMatrix route_involutive, bareOracle_apply,
    applyGate_permMatrix route_involutive, route_involutive]

theorem workspacePhase_apply (f : I → Bool) (ψ : QState (Data I W)) (q : Data I W) :
    ApplyGate (workspacePhaseOracle f) ψ q =
      (if q.1.2 && f q.1.1 then (-1 : ℂ) else 1) * ψ q := by
  rw [workspacePhaseOracle, applyGate_tensorGate_one, applyGate_phaseOracle]

theorem routed_bare_reference (f : I → Bool) (r : I) (hfr : f r = false)
    (ψ : QState (Data I W)) :
    ApplyGate routeGate (ApplyGate (bareOracle f) (ApplyGate routeGate (referenceInput r ψ))) =
      referenceInput r (ApplyGate (workspacePhaseOracle f) ψ) := by
  funext q
  rcases q with ⟨⟨⟨x, b⟩, w⟩, s⟩
  rw [routed_bare_apply]
  change (if f (route (((x, b), w), s)).2 then (-1 : ℂ) else 1) *
      (ψ ((x, b), w) * Ket r s) =
    ApplyGate (workspacePhaseOracle f) ψ ((x, b), w) * Ket r s
  rw [workspacePhase_apply]
  by_cases hs : s = r
  · subst s
    cases b <;> simp [route, hfr]
  · simp [Qatlib.Foundations.PureStateMath.Ket, hs]

theorem lifted_gate_reference (U : Matrix (Data I W) (Data I W) ℂ)
    (r : I) (ψ : QState (Data I W)) :
    ApplyGate (TensorGate U (1 : Matrix I I ℂ)) (referenceInput r ψ) =
      referenceInput r (ApplyGate U ψ) := by
  rw [referenceInput, applyGate_tensorGate, applyGate_one]
  rfl

def dataHadamard : Matrix (Full I W) (Full I W) ℂ :=
  TensorGate (controlHadamard (I := I) (W := W)) (1 : Matrix I I ℂ)

theorem dataHadamard_unitary : dataHadamard (I := I) (W := W) ∈ unitaryGroup (Full I W) ℂ := by
  apply tensorGate_unitary
  · unfold controlHadamard
    exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
      (Submonoid.one_mem _)
  · exact Submonoid.one_mem _

def oneBitCircuit : Circuit (Full I W) :=
  [Step.gate dataHadamard, Step.gate routeGate, Step.query,
    Step.gate routeGate, Step.gate dataHadamard]

theorem oneBitCircuit_unitary : IsUnitaryCircuit (oneBitCircuit (I := I) (W := W)) := by
  simp only [oneBitCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil]
  exact ⟨dataHadamard_unitary, routeGate_unitary, routeGate_unitary, dataHadamard_unitary, trivial⟩

theorem oneBitCircuit_queries : QueryCount (oneBitCircuit (I := I) (W := W)) = 1 := by
  rfl

theorem run_oneBitCircuit (f : I → Bool) (r : I) (hfr : f r = false)
    (ψ : QState (Data I W)) :
    Run (bareOracle f) oneBitCircuit (referenceInput r ψ) =
      referenceInput r (ApplyGate (workspaceBitOracle f) ψ) := by
  simp only [oneBitCircuit, run_gate, run_query, run_nil]
  change ApplyGate (TensorGate controlHadamard (1 : Matrix I I ℂ))
    (ApplyGate routeGate (ApplyGate (bareOracle f) (ApplyGate routeGate
      (ApplyGate (TensorGate controlHadamard (1 : Matrix I I ℂ)) (referenceInput r ψ))))) = _
  rw [lifted_gate_reference, routed_bare_reference f r hfr, lifted_gate_reference]
  congr 1
  rw [← applyGate_mul, ← applyGate_mul, controlHadamard_mul_phase_mul_controlHadamard]

end Qatlib.Concepts.CompressedQuery.CompressOracle
