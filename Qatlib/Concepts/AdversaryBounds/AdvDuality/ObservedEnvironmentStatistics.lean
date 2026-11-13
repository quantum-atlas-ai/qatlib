/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedEnvironment
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalUnitaryDiscard

/-!
# Statistics under environment transformations

`reduceEnvironmentTrace` turns a pure branch on a product register into a mixed branch by taking
a partial trace, retaining its classical metadata. The module proves that a unitary acting on
the environment leaves this reduced branch unchanged, as expected from the partial trace
formalism in [Watrous2018].

Combining this invariance with `observed_environment_intertwining` yields equal reduced traces,
expected query counts, and event masses for the corresponding lifted executions. Events here
depend on acceptance and the measurement outcome record.

## Main statements

* `reduceEnvironmentTrace_environmentTrace` proves invariance of the reduced branch under an
  environment unitary.
* `observed_environment_reduced_traces` equates reduced branch lists under an oracle
  intertwining relation.
* `observed_environment_expected_queries_general` and `observed_environment_event_mass` preserve
  the corresponding scalar statistics.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- Converts a pure branch on system and environment registers to a mixed system branch by
partially tracing its outer product, retaining all classical metadata. -/
noncomputable def reduceEnvironmentTrace {d e : ℕ}
    (t : BranchTrace (Fin d × Fin e)) : MixedBranchTrace d :=
  ⟨PartialTrace (outerProduct t.state), t.accepted, t.queries, t.gates,
    t.measurements, t.outcomes⟩

/-- Applying a unitary to the environment of a pure branch leaves its reduced mixed trace
unchanged. -/
theorem reduceEnvironmentTrace_environmentTrace {d e : ℕ}
    (W : Operator e) (hW : W ∈ Matrix.unitaryGroup (Fin e) ℂ)
    (t : BranchTrace (Fin d × Fin e)) :
    reduceEnvironmentTrace (environmentTrace W t) = reduceEnvironmentTrace t := by
  unfold reduceEnvironmentTrace environmentTrace
  (try dsimp only)
  rw [partialTrace_outerProduct_apply_tensorRight t.state W hW]

/-- A unitary acting only on the environment preserves the total Born mass of a product-register
state. -/
theorem branchMass_apply_tensorRight {d e : ℕ}
    (W : Operator e) (hW : W ∈ Matrix.unitaryGroup (Fin e) ℂ)
    (psi : QState (Fin d × Fin e)) :
    branchMass (ApplyGate (TensorGate (1 : Operator d) W) psi) = branchMass psi :=
  measureProb_applyGate_univ
    (tensorGate_unitary (U := (1 : Operator d)) (Submonoid.one_mem _) hW) psi

/-- Oracles intertwined by an environment unitary yield equal reduced trace lists when their
initial states are related by that unitary. -/
theorem observed_environment_reduced_traces {d e : ℕ}
    (W : Operator e) (hW : W ∈ Matrix.unitaryGroup (Fin e) ℂ)
    (A B : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (hAB : A * TensorGate (1 : Operator d) W =
      TensorGate (1 : Operator d) W * B)
    (P : ObservedCircuit (Fin d)) (psi : QState (Fin d × Fin e)) :
    (observedTraces A (liftObservedEnvironment (E := Fin e) P)
      (ApplyGate (TensorGate (1 : Operator d) W) psi)).map reduceEnvironmentTrace =
    (observedTraces B (liftObservedEnvironment (E := Fin e) P) psi).map
      reduceEnvironmentTrace := by
  rw [observed_environment_intertwining W A B hAB P psi]
  simp only [List.map_map, Function.comp_def,
    reduceEnvironmentTrace_environmentTrace W hW]

/-- For finite-dimensional system and environment registers, an environment unitary intertwining
the oracles preserves expected queries on the correspondingly transformed input. -/
theorem observed_environment_expected_queries {d e : ℕ}
    (W : Operator e) (hW : W ∈ Matrix.unitaryGroup (Fin e) ℂ)
    (A B : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (hAB : A * TensorGate (1 : Operator d) W =
      TensorGate (1 : Operator d) W * B)
    (P : ObservedCircuit (Fin d)) (psi : QState (Fin d × Fin e)) :
    expectedObservedQueries A (liftObservedEnvironment (E := Fin e) P)
      (ApplyGate (TensorGate (1 : Operator d) W) psi) =
    expectedObservedQueries B (liftObservedEnvironment (E := Fin e) P) psi := by
  simp only [expectedObservedQueries_eq_sum]
  rw [observed_environment_intertwining W A B hAB P psi]
  simp only [List.map_map, Function.comp_def, environmentTrace,
    branchMass_apply_tensorRight W hW]

/-- For arbitrary finite index types, an environment unitary intertwining the oracles preserves
expected queries on the correspondingly transformed input. -/
theorem observed_environment_expected_queries_general
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (W : Matrix E E ℂ) (hW : W ∈ Matrix.unitaryGroup E ℂ)
    (A B : Matrix (I × E) (I × E) ℂ)
    (hAB : A * TensorGate (1 : Matrix I I ℂ) W =
      TensorGate (1 : Matrix I I ℂ) W * B)
    (P : ObservedCircuit I) (psi : QState (I × E)) :
    expectedObservedQueries A (liftObservedEnvironment (E := E) P)
      (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi) =
    expectedObservedQueries B (liftObservedEnvironment (E := E) P) psi := by
  have hm (phi : QState (I × E)) :
      branchMass (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) phi) = branchMass phi :=
    measureProb_applyGate_univ (tensorGate_unitary (Submonoid.one_mem _) hW) phi
  simp only [expectedObservedQueries_eq_sum]
  rw [observed_environment_intertwining W A B hAB P psi]
  simp only [List.map_map, Function.comp_def, environmentTrace, hm]

/-- An environment unitary intertwining the oracles preserves the mass of every event determined
by acceptance and the outcome record, with the initial state transformed accordingly. -/
theorem observed_environment_event_mass
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (W : Matrix E E ℂ) (hW : W ∈ Matrix.unitaryGroup E ℂ)
    (A B : Matrix (I × E) (I × E) ℂ)
    (hAB : A * TensorGate (1 : Matrix I I ℂ) W =
      TensorGate (1 : Matrix I I ℂ) W * B)
    (P : ObservedCircuit I) (psi : QState (I × E))
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass A (liftObservedEnvironment (E := E) P)
      (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi)
      (fun t => event t.accepted t.outcomes) =
    observedEventMass B (liftObservedEnvironment (E := E) P) psi
      (fun t => event t.accepted t.outcomes) := by
  have hm (phi : QState (I × E)) :
      branchMass (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) phi) = branchMass phi :=
    measureProb_applyGate_univ (tensorGate_unitary (Submonoid.one_mem _) hW) phi
  unfold observedEventMass
  rw [observed_environment_intertwining W A B hAB P psi]
  simp only [List.map_map, Function.comp_def, environmentTrace, hm]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
