/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryPreparation

/-!
# Three-source words for a paid physical history

`sources` supplies separate Hamiltonian, purification preparation, and projector ports on a
common history register. `instructions` combines a single paid preparation call, seven
initialization gates, physical-time simulation, and a single projector call.

The output and event identities connect this explicit word to the actual projector-history
probability used by amplitude estimation [BrassardEtAl2002].

## Main statements

* `instructions_counts`: preparation and projector each cost one call, with seven initialization
  gates.
* `actual_output`: the evaluated word gives the physical projector-history state after
  relabeling.
* `actual_probability`: the word amplitude equals the physical zero-projector-ancilla
  probability.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryWord
open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Interval Matrix.Norms.L2Operator

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
open PaidHistoryPreparation

noncomputable local instance executionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q (Reg a × I)) :=
  BinaryClockSingleCU.newDecidableEq q (Reg a × I)

/-- The Hamiltonian simulation, paid purification preparation, and projector matrices acting on
the common full history register. -/
def sources (q a m : ℕ) (UH : Matrix (Reg a × I) (Reg a × I) ℂ)
    (P : Matrix (E × I) (E × I) ℂ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source →
      Matrix (Whole q a m I E) (Whole q a m I E) ℂ
  | .hamiltonian => parallelOracle (J := Reg m) (BinaryClockPurifier.oracle (E := E) q UH)
  | .preparation => preparationPort q a m P
  | .projector => BinaryClockProjectorReadout.projectorPort q a m UPi

/-- The purified physical-time simulation word extended by the projector ancilla, concatenated
with the known-register initialization. -/
def body (q a m : ℕ) (α T : ℚ) (k : ℕ) :
    List (AdjointStep (Whole q a m I E)) :=
  phaseLiftWord (parallelOracle (J := Reg m))
    (BinaryClockPurifier.instructions (E := E) q (encodingFiber (I := I) (ZeroStr a)) α T k) ++
      initialization q a m

/-- The three-source history word combining paid preparation, initialization and simulation, and
projector access. -/
def instructions (q a m : ℕ) (α T : ℚ) (k : ℕ) :
    List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step
      (Whole q a m I E)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord
    (body q a m α T k)

/-- Evaluating the simulation word extended by the projector ancilla equals the identity
extension of the purified simulation matrix. -/
theorem simulation_evaluate (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ) :
    evaluate (parallelOracle (J := Reg m) (BinaryClockPurifier.oracle (E := E) q UH))
      (phaseLiftWord (parallelOracle (J := Reg m))
        (BinaryClockPurifier.instructions (E := E) q (encodingFiber (I := I) (ZeroStr a)) α T k)) =
      parallelOracle (J := Reg m) (evaluate (BinaryClockPurifier.oracle (E := E) q UH)
        (BinaryClockPurifier.instructions (E := E) q (encodingFiber (I := I) (ZeroStr a)) α T k)) :=
  phaseLiftWord_evaluate _ parallel_select_one (fun _ _ => (parallel_select_mul _ _).symm)
    (fun U => (parallelOracle_adjoint U).symm) _ _

/-- All three full-register source matrices are unitary when the supplied Hamiltonian,
preparation, and projector matrices are unitary. -/
theorem sources_unitary (q a m : ℕ)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ) (hH : UH ∈ Matrix.unitaryGroup _ ℂ)
    (P : Matrix (E × I) (E × I) ℂ) (hP : P ∈ Matrix.unitaryGroup _ ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (hPi : UPi ∈ Matrix.unitaryGroup _ ℂ) :
    ∀ s, sources q a m UH P UPi s ∈ Matrix.unitaryGroup (Whole q a m I E) ℂ := by
  intro s
  cases s with
  | hamiltonian =>
    change parallelOracle (J := Reg m) (BinaryClockPurifier.oracle (E := E) q UH) ∈
      Matrix.unitaryGroup (Whole q a m I E) ℂ
    apply parallelOracle_unitary
    change TensorGate (BinaryClockSingleCU.oracle q UH) (1 : Matrix E E ℂ) ∈ Matrix.unitaryGroup _ ℂ
    apply tensorGate_unitary
    · exact BinaryClockSingleCU.oracle_unitary q hH
    · exact Submonoid.one_mem _
  | preparation => exact preparationPort_unitary q a m P hP
  | projector => exact BinaryClockProjectorReadout.projectorPort_unitary q a m UPi hPi

/-- The paid history instruction word is well formed for the stated projected encoding of the
normalized Hermitian Hamiltonian. -/
theorem instructions_wellFormed (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ)
    (henc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) UH
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a))) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed
      (instructions (I := I) (E := E) q a m α T k) := by
  apply Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_wellFormed
  change WellFormedAdjointCircuit (_ ++ initialization (I := I) (E := E) q a m)
  apply WellFormedAdjointCircuit.append
  · exact phaseLiftWord_wellFormed (parallelOracle (J := Reg m))
      (fun (M : Matrix (BinaryClockProjectorReadout.Raw q a I E) _ ℂ) h => parallelOracle_unitary h)
      (BinaryClockPurifier.resources (E := E) q α T k H UH
        (encodingFiber (I := I) (ZeroStr a)) hH henc).1
  · exact (initialization_resources q a m).1

/-- The history word uses one preparation call, one projector call, the physical-time
simulator's Hamiltonian queries, and its gate count plus seven. -/
theorem instructions_counts (q a m : ℕ) (α T : ℚ) (k : ℕ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .hamiltonian
      (instructions (I := I) (E := E) q a m α T k) =
        adjointQueryCount (BinaryClockPhysicalTime.instructions q (encodingFiber (I := I) (ZeroStr a)) α T k) ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .preparation
      (instructions (I := I) (E := E) q a m α T k) = 1 ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .projector
      (instructions (I := I) (E := E) q a m α T k) = 1 ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount
      (instructions (I := I) (E := E) q a m α T k) =
        adjointGateCount (BinaryClockPhysicalTime.instructions q (encodingFiber (I := I) (ZeroStr a)) α T k) + 7 := by
  have h := Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_counts
    (body (I := I) (E := E) q a m α T k)
  simpa only [instructions, body, adjointQueryCount_append, adjointGateCount_append,
    (phaseLiftWord_counts (parallelOracle (J := Reg m)) _).1,
    (phaseLiftWord_counts (parallelOracle (J := Reg m)) _).2,
    BinaryClockPurifier.instructions, (phaseLiftWord_counts _ _).1, (phaseLiftWord_counts _ _).2,
    (initialization_resources (I := I) (E := E) q a m).2.1,
    (initialization_resources (I := I) (E := E) q a m).2.2, add_zero] using h

/-- An identity-extended matrix acts on an embedded basis fiber by applying the original matrix
inside that fiber. -/
theorem parallel_fiber {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix Y Y ℂ) (a : X) (v : QState Y) :
    parallelOracle (J := X) M *ᵥ (encodingFiber a *ᵥ v) = encodingFiber a *ᵥ (M *ᵥ v) := by
  funext x
  rcases x with ⟨c,y⟩
  unfold parallelOracle
  rw [BinaryClockSignalWord.select_mulVec]
  simp only [BinaryClockProjectorReadout.fiber_apply]
  by_cases h : c = a
  · simp only [h, if_true]
  · simp only [h, if_false]
    change (M *ᵥ (0 : QState Y)) y = 0
    rw [Matrix.mulVec_zero]
    rfl

/-- Relabeling the evaluated paid history word on its basis seed gives the actual
projector-history output for the supplied prepared purification. -/
theorem actual_output (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ) (P : Matrix (E × I) (E × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (s : E × I) :
    relabelState (BinaryClockProjectorReadout.outputEquiv q a m)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate
        (sources q a m UH P UPi) (instructions q a m α T k) *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (seed q a m s)) =
      BinaryClockProjectorReadout.actual q a m α T k UH UPi
        (P *ᵥ Qatlib.Foundations.PureStateMath.Ket s) := by
  rw [instructions,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_evaluate]
  change relabelState (BinaryClockProjectorReadout.outputEquiv q a m)
    ((BinaryClockProjectorReadout.projectorPort q a m UPi *
      evaluate (parallelOracle (J := Reg m) (BinaryClockPurifier.oracle (E := E) q UH))
        (body q a m α T k) * preparationPort q a m P) *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (seed q a m s)) = _
  simp only [body, evaluate_append, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  rw [preparation_on_seed, initialization_on_state, simulation_evaluate, parallel_fiber]
  rfl

/-- The full-history measurement event in which the projector ancilla equals the zero string. -/
def event (q a m : ℕ) : Finset (Whole q a m I E) := {x | x.1 = ZeroStr m}

/-- The three-source word's event amplitude equals the actual projector-history probability of a
zero projector ancilla. -/
theorem actual_probability (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ) (P : Matrix (E × I) (E × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (s : E × I) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude
      (sources q a m UH P UPi) (instructions q a m α T k) (seed q a m s) (event q a m) =
      MeasureProb (BinaryClockProjectorReadout.actual q a m α T k UH UPi
        (P *ᵥ Qatlib.Foundations.PureStateMath.Ket s)) {x | x.2.2.1 = ZeroStr m} := by
  rw [← actual_output q a m α T k UH P UPi s]
  have h := measureProb_relabelState (BinaryClockProjectorReadout.outputEquiv (I := I) (E := E) q a m)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate
      (sources q a m UH P UPi) (instructions q a m α T k) *ᵥ
        Qatlib.Foundations.PureStateMath.Ket (seed q a m s)) (event q a m)
  have he : (event (I := I) (E := E) q a m).map
      (BinaryClockProjectorReadout.outputEquiv q a m).toEmbedding =
      ({x : BinaryClockProjectorReadout.Result q a m I E | x.2.2.1 = ZeroStr m} : Finset _) := by
    ext x
    simp only [Finset.mem_map_equiv, event, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [he] at h
  exact h.symm

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryWord
