/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetworkDefs
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol

/-!
# Event instruments on encoded registers

This module packages computational-basis events as Hermitian projectors, binary POVMs, and
instruments. `encodedEventInstrument` transports a unitary followed by an event measurement to a
finite encoding; the qudit definitions describe decoded teleportation states and coarse outcome
events. For background, see [NielsenChuang2010].

## Main statements

* `basisEventInstrument`: a unitary followed by a binary event measurement.
* `quditCoarseInstrument`: coarse measurement of a specified pair of qudit outcomes.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.InstrumentCore.PovmBridge

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Matrix Qatlib.Concepts.InstrumentCore.PovmBridge
open scoped BigOperators ComplexOrder

/-- The computational-basis projector onto `S`, packaged as a Hermitian matrix. -/
def eventProjector {D : ℕ} (S : Finset (Fin D)) : HermitianMat (Fin D) ℂ :=
  ⟨Projector S, projector_conjTranspose S⟩

/-- The binary projective POVM for membership in the basis event `S`. -/
def eventPOVM {D : ℕ} (S : Finset (Fin D)) : POVM Bool (Fin D) :=
  binaryProjectivePOVM (eventProjector S) (projector_mul_self S)

/-- The instrument applying the unitary `U` and then measuring the basis event `S` with its
complementary outcome. -/
def basisEventInstrument {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (S : Finset (Fin D)) : Instrument Bool D D :=
  Instrument.ofBranches
    (fun o => ((Instrument.ofPOVM (eventPOVM S)).branch o).comp (conjBranch U))
    (fun o => ((Instrument.ofPOVM (eventPOVM S)).cp o).comp (completelyPositive_conjBranch U))
    (by
      intro A
      change Matrix.trace (∑ o, (Instrument.ofPOVM (eventPOVM S)).branch o (conjBranch U A)) = _
      rw [Instrument.total, trace_conjBranch_unitary U hU])

/-- The event instrument obtained by relabeling `U` and `S` through the finite encoding `e`. -/
def encodedEventInstrument {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) : Instrument Bool D D :=
  basisEventInstrument (relabelGate e U) ((relabelGate_mem_unitaryGroup e U).mpr hU)
    (S.map e.toEmbedding)

/-- The prepared qudit teleportation state after the inverse controlled-addition and inverse
Fourier decoding gates, in the encoded triple register. -/
def quditDecodedState (n : ℕ) [NeZero n] (ψ : QState (Fin n)) : QState (Fin (n*n*n)) :=
  (relabelGate (quditRegisterEquiv n) (quditHaInvB n * quditSUMabInvB n) *
    quditPreparedFrame n) *ᵥ ψ

/-- The encoded triple-register basis event whose first two qudit labels equal `o`. -/
def quditOutcomeEvent (n : ℕ) (o : Fin n × Fin n) : Finset (Fin (n*n*n)) :=
  (Finset.univ.filter (fun r : QuditTriple n => r.1 = o)).map (quditRegisterEquiv n).toEmbedding

/-- The binary instrument testing whether the first two decoded qudit labels equal the specified
outcome pair `o`. -/
def quditCoarseInstrument (n : ℕ) (o : Fin n × Fin n) : Instrument Bool (n*n*n) (n*n*n) :=
  basisEventInstrument 1 (by simp) (quditOutcomeEvent n o)

end Qatlib.Concepts.TensorRegisters.RegisterModel
