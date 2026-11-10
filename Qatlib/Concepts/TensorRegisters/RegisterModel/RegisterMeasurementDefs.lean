/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetworkDefs
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
set_option warningAsError false
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

def eventProjector {D : ℕ} (S : Finset (Fin D)) : HermitianMat (Fin D) ℂ :=
  ⟨Projector S, projector_conjTranspose S⟩

def eventPOVM {D : ℕ} (S : Finset (Fin D)) : POVM Bool (Fin D) :=
  binaryProjectivePOVM (eventProjector S) (projector_mul_self S)

def basisEventInstrument {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (S : Finset (Fin D)) : Instrument Bool D D :=
  Instrument.ofBranches
    (fun o => ((Instrument.ofPOVM (eventPOVM S)).branch o).comp (conjBranch U))
    (fun o => ((Instrument.ofPOVM (eventPOVM S)).cp o).comp (completelyPositive_conjBranch U))
    (by
      intro A
      change Matrix.trace (∑ o, (Instrument.ofPOVM (eventPOVM S)).branch o (conjBranch U A)) = _
      rw [Instrument.total, trace_conjBranch_unitary U hU])

def encodedEventInstrument {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) : Instrument Bool D D :=
  basisEventInstrument (relabelGate e U) ((relabelGate_mem_unitaryGroup e U).mpr hU)
    (S.map e.toEmbedding)

def quditDecodedState (n : ℕ) [NeZero n] (ψ : QState (Fin n)) : QState (Fin (n*n*n)) :=
  (relabelGate (quditRegisterEquiv n) (quditHaInvB n * quditSUMabInvB n) *
    quditPreparedFrame n) *ᵥ ψ

def quditOutcomeEvent (n : ℕ) (o : Fin n × Fin n) : Finset (Fin (n*n*n)) :=
  (Finset.univ.filter (fun r : QuditTriple n => r.1 = o)).map (quditRegisterEquiv n).toEmbedding

def quditCoarseInstrument (n : ℕ) (o : Fin n × Fin n) : Instrument Bool (n*n*n) (n*n*n) :=
  basisEventInstrument 1 (by simp) (quditOutcomeEvent n o)

end Qatlib.Concepts.TensorRegisters.RegisterModel
