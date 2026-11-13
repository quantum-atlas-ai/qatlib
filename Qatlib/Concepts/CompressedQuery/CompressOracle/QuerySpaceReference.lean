/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle

/-!
# Reference registers for bit query simulation

This module constructs a one-query simulation of a workspace bit oracle from a phase oracle on
an additional reference register. The controlled routing gate exchanges the query address with
the reference address when the target bit is true.

If the reference address has oracle value false, `run_oneBitCircuit` shows that routing and
target Hadamards implement the bit query and return the reference register to its original basis
state.

The mathematical context is discussed in [NielsenChuang2010].

## Main statements

* `routeGate_unitary`: Unitarity of controlled routing.
* `oneBitCircuit_queries`: The simulation uses exactly one oracle query.
* `run_oneBitCircuit`: The bit oracle simulation with a known false reference address.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The basis of algorithm registers consisting of an address, a Boolean target and a workspace
value. -/
abbrev Data (I W : Type) := (I × Bool) × W
/-- The algorithm basis extended by an additional reference address register. -/
abbrev Full (I W : Type) := Data I W × I

/-- Swap the query and reference addresses when the target bit is true, leaving the basis state
unchanged otherwise. -/
def route : Full I W → Full I W
  | (((x, false), w), r) => (((x, false), w), r)
  | (((x, true), w), r) => (((r, true), w), x)

omit [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- Applying controlled address routing twice returns the original basis state. -/
theorem route_involutive : Function.Involutive (route (I := I) (W := W)) := by
  rintro ⟨⟨⟨x, b⟩, w⟩, r⟩
  cases b <;> rfl

/-- The permutation matrix implementing controlled address routing. -/
def routeGate : Matrix (Full I W) (Full I W) ℂ := permMatrix route

/-- The controlled routing permutation matrix is unitary. -/
theorem routeGate_unitary : routeGate (I := I) (W := W) ∈ unitaryGroup (Full I W) ℂ :=
  permMatrix_unitary route_involutive

/-- The phase oracle acting only on the additional reference address register. -/
def bareOracle (f : I → Bool) : Matrix (Full I W) (Full I W) ℂ :=
  TensorGate (1 : Matrix (Data I W) (Data I W) ℂ) (PhaseOracle f)

/-- The phase oracle on the reference register is unitary. -/
theorem bareOracle_unitary (f : I → Bool) :
    bareOracle (W := W) f ∈ unitaryGroup (Full I W) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _) (phaseOracle_unitary f)

/-- The algorithm state tensored with the reference basis ket at `r`. -/
def referenceInput (r : I) (ψ : QState (Data I W)) : QState (Full I W) :=
  TensorState ψ (Ket r)

/-- The reference phase oracle multiplies each amplitude by −1 exactly when `f r` is true. -/
theorem bareOracle_apply (f : I → Bool) (v : QState (Full I W))
    (q : Data I W) (r : I) :
    ApplyGate (bareOracle f) v (q, r) = (if f r then (-1 : ℂ) else 1) * v (q, r) := by
  have hslice : ApplyGate (bareOracle f) v (q, r) =
      ApplyGate (PhaseOracle f) (fun x => v (q, x)) r := by
    simp [bareOracle, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.one_apply]
  rw [hslice, applyGate_phaseOracle]

/-- Conjugating the reference phase oracle by routing applies the sign determined by the
reference address of the routed basis state. -/
theorem routed_bare_apply (f : I → Bool) (v : QState (Full I W)) (q : Full I W) :
    ApplyGate routeGate (ApplyGate (bareOracle f) (ApplyGate routeGate v)) q =
      (if f (route q).2 then (-1 : ℂ) else 1) * v q := by
  change ApplyGate (permMatrix route) (ApplyGate (bareOracle f)
    (ApplyGate (permMatrix route) v)) q = _
  rw [applyGate_permMatrix route_involutive, bareOracle_apply,
    applyGate_permMatrix route_involutive, route_involutive]

/-- The workspace phase oracle multiplies an amplitude by −1 exactly when the target bit and the
queried function value are both true. -/
theorem workspacePhase_apply (f : I → Bool) (ψ : QState (Data I W)) (q : Data I W) :
    ApplyGate (workspacePhaseOracle f) ψ q =
      (if q.1.2 && f q.1.1 then (-1 : ℂ) else 1) * ψ q := by
  rw [workspacePhaseOracle, applyGate_tensorGate_one, applyGate_phaseOracle]

/-- At a reference address with function value false, the routed reference oracle implements the
controlled workspace phase oracle and preserves the reference ket. -/
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

/-- A gate lifted by the identity on the reference register acts only on the algorithm state and
preserves the reference ket. -/
theorem lifted_gate_reference (U : Matrix (Data I W) (Data I W) ℂ)
    (r : I) (ψ : QState (Data I W)) :
    ApplyGate (TensorGate U (1 : Matrix I I ℂ)) (referenceInput r ψ) =
      referenceInput r (ApplyGate U ψ) := by
  rw [referenceInput, applyGate_tensorGate, applyGate_one]
  rfl

/-- The target Hadamard gate lifted to act trivially on the reference register. -/
def dataHadamard : Matrix (Full I W) (Full I W) ℂ :=
  TensorGate (controlHadamard (I := I) (W := W)) (1 : Matrix I I ℂ)

/-- The lifted target Hadamard is unitary. -/
theorem dataHadamard_unitary : dataHadamard (I := I) (W := W) ∈ unitaryGroup (Full I W) ℂ := by
  apply tensorGate_unitary
  · unfold controlHadamard
    exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
      (Submonoid.one_mem _)
  · exact Submonoid.one_mem _

/-- The circuit consisting of a target Hadamard, routing, one query, routing and a final target
Hadamard. -/
def oneBitCircuit : Circuit (Full I W) :=
  [Step.gate dataHadamard, Step.gate routeGate, Step.query,
    Step.gate routeGate, Step.gate dataHadamard]

/-- Every ordinary gate in the one-query bit simulation circuit is unitary. -/
theorem oneBitCircuit_unitary : IsUnitaryCircuit (oneBitCircuit (I := I) (W := W)) := by
  simp only [oneBitCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil]
  exact ⟨dataHadamard_unitary, routeGate_unitary, routeGate_unitary, dataHadamard_unitary, trivial⟩

omit [Fintype I] [Fintype W] in

/-- The bit simulation circuit uses exactly one oracle query. -/
theorem oneBitCircuit_queries : QueryCount (oneBitCircuit (I := I) (W := W)) = 1 := by
  rfl

/-- If `f r` is false, the one-query circuit with the reference phase oracle implements the
workspace bit oracle while preserving the reference ket at `r`. -/
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
