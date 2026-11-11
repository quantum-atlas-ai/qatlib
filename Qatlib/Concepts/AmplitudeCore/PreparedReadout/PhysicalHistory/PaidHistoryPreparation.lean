/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorAccuracy
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE

/-!
# Paid purification and history-state initialization

This module places a supplied purification unitary on the environment and system registers while
keeping clock, projector ancilla, and simulator work registers explicit. `initialization`
supplies the clock Hadamard and the six-gate signal-frame initialization.

`initialization_on_state` identifies the resulting state with the framed logical history input.
The construction uses standard unitary preparation and purification conventions
[NielsenChuang2010].

## Main statements

* `preparation_on_seed`: the preparation port applies the supplied unitary to the
  environment-system seed.
* `initialization_resources`: initialization uses seven explicit gates and no oracle queries.
* `initialization_on_state`: the initialized state agrees with the purified clock simulator
  frame.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryPreparation
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
set_option warningAsError false

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- The complete history register containing the projector ancilla, raw simulator, and
purification environment. -/
abbrev Whole (q a m : ℕ) (I E : Type) := Reg m × BinaryClockProjectorReadout.Raw q a I E
noncomputable local instance executionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q (Reg a × I)) :=
  BinaryClockSingleCU.newDecidableEq q (Reg a × I)

/-- The projector ancilla, clock, and simulator work registers initialized independently of the
supplied purification. -/
abbrev Known (q a m : ℕ) := Reg m × (Reg q × BinaryClockCoordinateFrame.Work a)

/-- Rearrange the complete history register into known registers and the environment-system
register. -/
def prepEquiv (q a m : ℕ) : Whole q a m I E ≃ (Known q a m × (E × I)) where
  toFun x :=
    let y := BinaryClockCoordinateFrame.placement (I := I) (E := E) q a x.2
    ((x.1,(y.1,y.2.1.2)),(y.2.1.1,y.2.2))
  invFun y :=
    (y.1.1, (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a).symm
      (y.1.2.1,((y.2.1,y.1.2.2),y.2.2)))
  left_inv := by
    intro x
    change (x.1, (BinaryClockCoordinateFrame.placement q a).symm
      (BinaryClockCoordinateFrame.placement q a x.2)) = x
    rw [Equiv.symm_apply_apply]
  right_inv := by intro y; simp only [Equiv.apply_symm_apply]

/-- Extend the supplied purification matrix by the known-register identity and transport it to
the full history register. -/
def preparationPort (q a m : ℕ) (P : Matrix (E × I) (E × I) ℂ) :
    Matrix (Whole q a m I E) (Whole q a m I E) ℂ :=
  relabelGate (prepEquiv q a m).symm (parallelOracle (J := Known q a m) P)

/-- Extend a signal initialization matrix to the appropriate simulator work registers within the
full history register. -/
def simulatorGate (q a m : ℕ)
    (M : Matrix (BinaryClockSignalWord.SimulatorSpace (Reg a))
      (BinaryClockSignalWord.SimulatorSpace (Reg a)) ℂ) :
    Matrix (Whole q a m I E) (Whole q a m I E) ℂ :=
  relabelGate (prepEquiv q a m).symm
    (TensorGate (TensorGate (1 : Matrix (Reg m) (Reg m) ℂ)
      (TensorGate (1 : Matrix (Reg q) (Reg q) ℂ)
        (TensorGate (1 : Matrix Bool Bool ℂ) (TensorGate (1 : Matrix Bool Bool ℂ) M))))
      (1 : Matrix (E × I) (E × I) ℂ))

/-- Apply the `q`-qubit Hadamard to the clock and the identity to every other history register. -/
def clockGate (q a m : ℕ) : Matrix (Whole q a m I E) (Whole q a m I E) ℂ :=
  relabelGate (prepEquiv q a m).symm
    (TensorGate (TensorGate (1 : Matrix (Reg m) (Reg m) ℂ)
      (TensorGate (HadamardN q) (1 : Matrix (BinaryClockCoordinateFrame.Work a)
        (BinaryClockCoordinateFrame.Work a) ℂ))) (1 : Matrix (E × I) (E × I) ℂ))

/-- The clock Hadamard followed in matrix product order by the lifted six-gate signal
initialization word. -/
def initialization (q a m : ℕ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Whole q a m I E)) :=
  [.gate (clockGate q a m)] ++
    phaseLiftWord (simulatorGate q a m) (BinaryClockSignalInitialization.word (H := Reg a))

/-- Extending simulator initialization matrices to the full history register preserves
multiplication. -/
theorem simulatorGate_mul (q a m : ℕ) (M N : Matrix
    (BinaryClockSignalWord.SimulatorSpace (Reg a))
    (BinaryClockSignalWord.SimulatorSpace (Reg a)) ℂ) :
    simulatorGate (I := I) (E := E) q a m (M*N) =
      simulatorGate q a m M * simulatorGate q a m N := by
  simp only [simulatorGate, ← CircuitRelabel.relabelGate_mul, tensorGate_mul,
    Matrix.one_mul]

/-- Extending the identity simulator matrix gives the identity on the full history register. -/
theorem simulatorGate_one (q a m : ℕ) :
    simulatorGate (I := I) (E := E) q a m 1 = 1 := by
  simp only [simulatorGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- The conjugate transpose of a relabeled matrix equals the relabeling of its conjugate
transpose. -/
private theorem relabel_adjoint {X Y : Type} (e : X ≃ Y) (M : Matrix X X ℂ) :
    (relabelGate e M)ᴴ = relabelGate e Mᴴ := by
  ext x y
  rfl

/-- Extending a simulator initialization matrix to the full history register commutes with
conjugate transpose. -/
theorem simulatorGate_adjoint (q a m : ℕ) (M : Matrix
    (BinaryClockSignalWord.SimulatorSpace (Reg a))
    (BinaryClockSignalWord.SimulatorSpace (Reg a)) ℂ) :
    simulatorGate (I := I) (E := E) q a m Mᴴ = (simulatorGate q a m M)ᴴ := by
  simp only [simulatorGate, relabel_adjoint, tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- The initialization word evaluates to the clock gate times the extended signal initialization
matrix, independently of the oracle. -/
theorem initialization_evaluate (q a m : ℕ)
    (V : Matrix (Whole q a m I E) (Whole q a m I E) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate V (initialization q a m) = clockGate q a m *
      simulatorGate q a m (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate 1 (BinaryClockSignalInitialization.word (H := Reg a))) := by
  simp only [initialization, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix,
    Matrix.mul_one]
  have hv : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate V (phaseLiftWord (simulatorGate q a m)
      (BinaryClockSignalInitialization.word (H := Reg a))) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (simulatorGate q a m 1) (phaseLiftWord (simulatorGate q a m)
        (BinaryClockSignalInitialization.word (H := Reg a))) := rfl
  rw [hv, phaseLiftWord_evaluate _ (simulatorGate_one q a m)
    (simulatorGate_mul q a m) (simulatorGate_adjoint q a m)]

/-- The known-register seed with zero projector and clock registers, five false flags, and zero
encoding ancillas. -/
def knownSeed (q a m : ℕ) : Known q a m :=
  (ZeroStr m,(ZeroStr q,(false,(false,(false,(false,(false,ZeroStr a)))))))

/-- Place an environment-system basis label alongside `knownSeed` and convert it into full
history coordinates. -/
def seed (q a m : ℕ) (s : E × I) : Whole q a m I E :=
  (prepEquiv q a m).symm (knownSeed q a m,s)

omit [Fintype I] [Fintype E] in

/-- Relabeling the tensor product of the known basis seed and the supplied basis seed gives the
full history basis seed. -/
theorem seed_layout (q a m : ℕ) (s : E × I) :
    relabelState (prepEquiv q a m).symm
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m))
        (Qatlib.Foundations.PureStateMath.Ket s)) =
      Qatlib.Foundations.PureStateMath.Ket (seed q a m s) := by
  funext x
  simp only [relabelState, TensorState, Qatlib.Foundations.PureStateMath.Ket,
    seed, Function.comp_apply, Equiv.symm_symm]
  have hx : x = (prepEquiv q a m).symm (knownSeed q a m,s) ↔
      (prepEquiv q a m x).1 = knownSeed q a m ∧ (prepEquiv q a m x).2 = s := by
    rw [Equiv.eq_symm_apply, Prod.ext_iff]
  simp only [hx]
  split_ifs <;> simp_all

/-- The preparation port sends the full basis seed to the supplied prepared state tensored with
the unchanged known-register seed. -/
theorem preparation_on_seed (q a m : ℕ) (P : Matrix (E × I) (E × I) ℂ)
    (s : E × I) :
    preparationPort q a m P *ᵥ Qatlib.Foundations.PureStateMath.Ket (seed q a m s) =
      relabelState (prepEquiv q a m).symm
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m))
          (P *ᵥ Qatlib.Foundations.PureStateMath.Ket s)) := by
  rw [← seed_layout q a m s]
  exact (applyGate_relabelGate (prepEquiv q a m).symm
    (parallelOracle (J := Known q a m) P)
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m))
      (Qatlib.Foundations.PureStateMath.Ket s))).trans
    (congrArg (relabelState (prepEquiv q a m).symm) (by
      funext x
      rcases x with ⟨w,v⟩
      change (parallelOracle (J := Known q a m) P *ᵥ _) (w,v) = _
      unfold parallelOracle
      rw [BinaryClockSignalWord.select_mulVec]
      simp only [TensorState, Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring))

/-- The preparation port is unitary whenever the supplied purification matrix is unitary. -/
theorem preparationPort_unitary (q a m : ℕ) (P : Matrix (E × I) (E × I) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (E × I) ℂ) :
    preparationPort q a m P ∈ Matrix.unitaryGroup (Whole q a m I E) ℂ :=
  (relabelGate_mem_unitaryGroup (prepEquiv q a m).symm _).2 (parallelOracle_unitary hP)

/-- Extending a unitary signal initialization matrix to the full history register preserves
unitarity. -/
theorem simulatorGate_unitary (q a m : ℕ) (M : Matrix
    (BinaryClockSignalWord.SimulatorSpace (Reg a))
    (BinaryClockSignalWord.SimulatorSpace (Reg a)) ℂ)
    (hM : M ∈ Matrix.unitaryGroup _ ℂ) :
    simulatorGate (I := I) (E := E) q a m M ∈ Matrix.unitaryGroup _ ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (simulatorGate q a m M)ᴴ * simulatorGate q a m M = 1
  rw [← simulatorGate_adjoint, ← simulatorGate_mul]
  have hm : Mᴴ * M = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hM
  rw [hm, simulatorGate_one]

/-- The full-register clock Hadamard gate is unitary. -/
theorem clockGate_unitary (q a m : ℕ) :
    clockGate (I := I) (E := E) q a m ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup (prepEquiv q a m).symm _).2
    (tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary (hadamardN_unitary q) (Submonoid.one_mem _))) (Submonoid.one_mem _))

/-- The history initialization word is well formed, makes no oracle queries, and contains
exactly seven explicit gates. -/
theorem initialization_resources (q a m : ℕ) :
    WellFormedAdjointCircuit (initialization (I := I) (E := E) q a m) ∧
      adjointQueryCount (initialization (I := I) (E := E) q a m) = 0 ∧
      adjointGateCount (initialization (I := I) (E := E) q a m) = 7 := by
  have h := BinaryClockSignalInitialization.resources (H := Reg a)
  refine ⟨?_, ?_, ?_⟩
  · apply WellFormedAdjointCircuit.append
    · simpa only [WellFormedAdjointCircuit.gate_cons_iff,
        WellFormedAdjointCircuit.nil, and_true] using! clockGate_unitary (I := I) (E := E) q a m
    · exact phaseLiftWord_wellFormed (simulatorGate q a m)
        (simulatorGate_unitary q a m) h.1
  · simp only [initialization, adjointQueryCount_append,
      (phaseLiftWord_counts (simulatorGate q a m) _).1, h.2.2.1]
    rfl
  · simp only [initialization, adjointGateCount_append,
      (phaseLiftWord_counts (simulatorGate q a m) _).2, h.2.2.2]
    rfl

/-- The known-register initialization matrix, combining the clock Hadamard with the signal
initialization and spectator identities. -/
def knownMatrix (q a m : ℕ) : Matrix (Known q a m) (Known q a m) ℂ :=
  TensorGate (1 : Matrix (Reg m) (Reg m) ℂ)
    (TensorGate (HadamardN q) (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ)
        (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate 1
          (BinaryClockSignalInitialization.word (H := Reg a))))))

/-- The full initialization matrix is the transported tensor product of `knownMatrix` with the
environment-system identity. -/
theorem initialization_matrix (q a m : ℕ)
    (V : Matrix (Whole q a m I E) (Whole q a m I E) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate V (initialization q a m) =
      relabelGate (prepEquiv q a m).symm
        (TensorGate (knownMatrix q a m) (1 : Matrix (E × I) (E × I) ℂ)) := by
  rw [initialization_evaluate]
  simp only [clockGate, simulatorGate, ← CircuitRelabel.relabelGate_mul,
    tensorGate_mul, Matrix.one_mul, Matrix.mul_one, knownMatrix]

/-- The known-register state with zero projector ancilla, uniform clock, and work state `eta a`. -/
def knownOutput (q a m : ℕ) : QState (Known q a m) := fun x =>
  Qatlib.Foundations.PureStateMath.Ket (ZeroStr m) x.1 *
    (Uniform (Reg q) x.2.1 * BinaryClockCoordinateFrame.eta a x.2.2)

/-- The signal initialization column at the all-zero seed has amplitude `i/2` when the first
flag and encoding ancillas vanish, and zero otherwise. -/
theorem simulator_column (a : ℕ) (u b c : Bool) (anc : Reg a) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate 1
      (BinaryClockSignalInitialization.word (H := Reg a)) (u,(b,(c,anc)))
        (false,(false,(false,ZeroStr a))) =
      if u = false ∧ anc = ZeroStr a then Complex.I / 2 else 0 := by
  have h := congrArg (fun F => F (u,(b,(c,anc))) (ZeroStr a))
    (BinaryClockSignalInitialization.intertwining
      (1 : Matrix (BinaryClockSignalWord.SimulatorSpace (Reg a)) _ ℂ)
      (1 : Matrix (Reg a) (Reg a) ℂ))
  simpa [BinaryClockSignalInitialization.baseFrame, Matrix.mul_apply,
    Fintype.sum_prod_type, BinaryClockSignalInitialization.simulatorFrame_entry,
    Matrix.one_apply, ite_mul, mul_ite, BinaryClockCoordinateFrame.average_phase,
    ite_and] using! h

/-- The known-register initialization matrix sends `knownSeed` to `knownOutput`. -/
theorem knownMatrix_on_seed (q a m : ℕ) :
    knownMatrix q a m *ᵥ Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m) =
      knownOutput q a m := by
  funext x
  rcases x with ⟨b,z,t,e,u,c,d,anc⟩
  have hc := congrArg (fun v => v z) (applyGate_hadamardN_ket_zero q)
  change ApplyGate (HadamardN q)
      (Qatlib.Foundations.PureStateMath.Ket (ZeroStr q)) z = Uniform (Reg q) z at hc
  rw [applyGate_eq_mulVec_ket] at hc
  change ApplyGate (knownMatrix q a m)
      (Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m)) _ = _
  rw [applyGate_eq_mulVec_ket]
  simp only [knownMatrix, knownSeed, tensorGate_apply, Matrix.one_apply, simulator_column,
    knownOutput, Qatlib.Foundations.PureStateMath.Ket, BinaryClockCoordinateFrame.eta,
    hc]
  split_ifs <;> simp_all

/-- Initializing the known registers alongside any purification gives the zero projector ancilla
tensored with the framed logical clock input. -/
theorem initialization_on_state (q a m : ℕ) (ψ : QState (E × I))
    (V : Matrix (Whole q a m I E) (Whole q a m I E) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate V (initialization q a m) *ᵥ
      relabelState (prepEquiv q a m).symm
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (knownSeed q a m)) ψ) =
      encodingFiber (ZeroStr m) *ᵥ
        (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ
          BinaryClockProjectorReadout.logicalState q ψ) := by
  rw [initialization_matrix, show _ *ᵥ relabelState _ _ = _ from
    applyGate_relabelGate (prepEquiv q a m).symm _ _]
  rw [applyGate_tensorGate,
    applyGate_one]
  change relabelState _ (TensorState (knownMatrix q a m *ᵥ _) ψ) = _
  rw [knownMatrix_on_seed]
  funext x
  rcases x with ⟨obs,⟨t,z,e,u,b,c,anc,i⟩,r⟩
  rw [BinaryClockProjectorReadout.fiber_apply,
    BinaryClockCoordinateFrame.frame_apply, BinaryClockProjectorReadout.logicalState_apply]
  simp [relabelState, prepEquiv, BinaryClockCoordinateFrame.placement, TensorState,
    knownOutput, Qatlib.Foundations.PureStateMath.Ket, mul_assoc, mul_left_comm]

/-- Applying a unitary preparation matrix to a basis seed gives a normalized purification. -/
theorem prepared_normalized (P : Matrix (E × I) (E × I) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (E × I) ℂ) (seed : E × I) :
    Normalized (P *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) :=
  normalized_applyGate hP (normalized_ket seed)

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryPreparation
