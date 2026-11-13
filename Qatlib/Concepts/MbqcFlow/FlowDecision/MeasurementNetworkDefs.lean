/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation

/-!
# Finite measurement networks and message trees

`FiniteNetwork` describes finite adaptive executions with instrument measurements, explicit bit
transmissions, and corrected qudit teleportation. Its dependent transcripts determine event
lists and `ExecutionResources`, while `feedForwardBranch` and `Clause8Claim` specify
conditional-unitary and reference-system behavior.

`BinaryMessageTree` represents finite messages by leaf paths and provides encoding and partial
decoding. `OneWayGuessingProtocol` describes input-dependent local instruments and
message-dependent guessing, in the quantum-information framework of [Watrous2018] and the
teleportation setting of [BennettEtAl1993Teleportation].

## Main statements

* `FiniteNetwork.Transcript`, `FiniteNetwork.events`, and `FiniteNetwork.resources`: execution
  records.
* `BinaryMessageTree.encode` and `BinaryMessageTree.decode`: tree-message representations.
* `OneWayGuessingProtocol.success`: prior-weighted guessing success.
* `Clause8Claim`: conditional-unitary, teleportation, and ledger properties.

## References

* [Watrous, 2018][Watrous2018]
* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open Qatlib
open scoped ComplexOrder

/-- The branch map obtained by applying an instrument branch and then conjugating by its
outcome-selected matrix. -/
noncomputable def feedForwardBranch {O : Type*} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Matrix (Fin E) (Fin E) ℂ) (o : O) :
    Operator D →ₗ[ℂ] Operator E :=
  (conjBranch (U o)).comp (I.branch o)

/-- A ledger recording created and consumed EPR pairs, loaded inputs, local measurements, and
transmitted classical bits. -/
structure NetworkResourceLedger where
  eprCreated : ℕ
  sharedEprUsed : ℕ
  inputsLoaded : ℕ
  localMeasurements : ℕ
  classicalBits : ℕ

/-- The condition that consumed shared EPR pairs do not exceed the number recorded as created. -/
def NetworkResourceLedger.EntanglementLaw (L : NetworkResourceLedger) : Prop :=
  L.sharedEprUsed ≤ L.eprCreated

/-- The conjunction of conditional-unitary instrument laws, corrected qudit teleportation
formulas with a reference system, and the resource-ledger entanglement condition. -/
def Clause8Claim : Prop :=
  (∀ (O : Type) [Fintype O] [DecidableEq O] (D E : ℕ)
    (I : Instrument O D E) (U : O → Matrix (Fin E) (Fin E) ℂ)
    (_hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ),
    ∃ J : Instrument O D E,
      (∀ (o : O) (ρ : Operator D), J.branch o ρ = (U o) * (I.branch o ρ) * (U o)ᴴ) ∧
      (∀ (ρ : Operator D), J.forget.map ρ = ∑ o, (U o) * (I.branch o ρ) * (U o)ᴴ) ∧
      (∀ R (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        partialTraceFirst (∑ o, tensorLeft (J.branch o) ρ) = partialTraceFirst ρ) ∧
      (∀ (ρ : Operator D) (o : O), ρ.PosSemidef → instrumentProb J ρ o = 0 → J.branch o ρ = 0)) ∧
  (∀ (n : ℕ) [NeZero n] (R : ℕ) (ρ : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) (o : Fin n × Fin n),
    quditActualReferenceCore n R o ρ = ((1 : ℂ) / (n : ℂ) ^ 2) • ρ ∧
    tensorLeft ((quditCorrectedInstrument n).branch o) ρ = ((1 : ℂ) / (n : ℂ) ^ 2) • ρ ∧
    (∑ o' : Fin n × Fin n, quditActualReferenceCore n R o' ρ) = ρ) ∧
  (∀ (L : NetworkResourceLedger),
    L.EntanglementLaw ↔ L.sharedEprUsed ≤ L.eprCreated)

end Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs

/-- Finite adaptive networks indexed by input and output dimension, with termination, instrument
measurement, classical transmission, and corrected qudit teleportation nodes. -/
inductive FiniteNetwork : ℕ → ℕ → Type where
  | done (D : ℕ) : FiniteNetwork D D
  | measure {D M E : ℕ} (s : ℕ) (I : Instrument (Fin s) D M)
      (next : Fin s → FiniteNetwork M E) : FiniteNetwork D E
  | send {D E : ℕ} (bits : List Bool) (next : FiniteNetwork D E) : FiniteNetwork D E
  | teleport {n E : ℕ} (hn : NeZero n) (width : ℕ) (fits : n ≤ 2 ^ width)
      (next : Fin n × Fin n → FiniteNetwork n E) : FiniteNetwork n E

/-- The dependent type of outcome transcripts for a finite network, recording measurement and
teleportation outcomes along the chosen continuation. -/
def FiniteNetwork.Transcript {D E : ℕ} : FiniteNetwork D E → Type
  | .done _ => Unit
  | .measure s _ next => (o : Fin s) × (next o).Transcript
  | .send _ next => next.Transcript
  | .teleport (n := n) _ _ _ next => (o : Fin n × Fin n) × (next o).Transcript

noncomputable instance FiniteNetwork.transcriptFintype {D E : ℕ} (P : FiniteNetwork D E) :
    Fintype P.Transcript := by
  induction P with
  | done D => exact inferInstanceAs (Fintype Unit)
  | measure s I next ih =>
      letI := ih
      exact inferInstanceAs (Fintype ((o : Fin s) × (next o).Transcript))
  | send bits next ih => exact ih
  | teleport hn width fits next ih =>
      letI := ih
      exact inferInstanceAs (Fintype ((o : _ × _) × (next o).Transcript))

/-- Execution events recording an instrument outcome, a transmitted bit string, or a qudit
teleportation outcome. -/
inductive NetworkEvent where
  | instrument (outcomes report : ℕ)
  | transmit (bits : List Bool)
  | teleport (n : ℕ) (hn : NeZero n) (outcome : Fin n × Fin n)

/-- The ordered event list associated with a network transcript, including the classical message
sent after each teleportation. -/
def FiniteNetwork.events {D E : ℕ} (P : FiniteNetwork D E) :
    P.Transcript → List NetworkEvent :=
  match P with
  | .done _ => fun _ => []
  | .measure s _ next => fun t =>
      .instrument s t.1.val :: (next t.1).events t.2
  | .send bits next => fun t => .transmit bits :: next.events t
  | .teleport (n := n) hn width _ next => fun t =>
      .teleport n hn t.1 :: .transmit (quditMessage n width t.1) :: (next t.1).events t.2

/-- Resource counts for abstract instrument calls, fresh pair dimensions, Bell pairs, matrix
gates, macro measurements, and classical bits. -/
structure ExecutionResources where
  abstractInstrumentCalls : ℕ := 0
  freshPairDimensions : List ℕ := []
  bellPairsPrepared : ℕ := 0
  matrixGates : ℕ := 0
  macroMeasurements : ℕ := 0
  classicalBits : ℕ := 0
  deriving DecidableEq

/-- The resource totals accumulated from an event list, including the implementation cost of
each teleportation event. -/
noncomputable def eventResources : List NetworkEvent → ExecutionResources
  | [] => {}
  | .instrument _ _ :: es =>
      let r := eventResources es
      { r with abstractInstrumentCalls := r.abstractInstrumentCalls + 1 }
  | .transmit bits :: es =>
      let r := eventResources es
      { r with classicalBits := bits.length + r.classicalBits }
  | .teleport n hn o :: es =>
      letI := hn
      let r := eventResources es
      { r with
        freshPairDimensions := n :: r.freshPairDimensions
        bellPairsPrepared := (if n = 2 then 1 else 0) + r.bellPairsPrepared
        matrixGates := (quditProgramLeaf n o).gates + r.matrixGates
        macroMeasurements := (quditProgramLeaf n o).measurements + r.macroMeasurements }

/-- The resource record obtained by accumulating the events of a network transcript. -/
noncomputable def FiniteNetwork.resources {D E : ℕ} (P : FiniteNetwork D E)
    (t : P.Transcript) : ExecutionResources := eventResources (P.events t)

/-- The list of bit strings carried by transmission events, preserving their order. -/
def transmittedWords (es : List NetworkEvent) : List (List Bool) :=
  es.filterMap fun e => match e with
    | .transmit bits => some bits
    | _ => none

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs

/-- Finite binary trees representing messages as paths from the root to a leaf. -/
inductive BinaryMessageTree where
  | leaf
  | fork (left right : BinaryMessageTree)

/-- The type of leaf paths of a binary message tree, choosing a left or right subtree at each
fork. -/
def BinaryMessageTree.Path : BinaryMessageTree → Type
  | .leaf => Unit
  | .fork l r => l.Path ⊕ r.Path

noncomputable instance BinaryMessageTree.pathFintype (T : BinaryMessageTree) : Fintype T.Path := by
  induction T with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | fork l r ihl ihr =>
      letI := ihl
      letI := ihr
      exact inferInstanceAs (Fintype (l.Path ⊕ r.Path))

/-- The maximum number of forks on a path from the root to a leaf. -/
def BinaryMessageTree.depth : BinaryMessageTree → ℕ
  | .leaf => 0
  | .fork l r => max l.depth r.depth + 1

/-- The bit-string encoding of a leaf path, using `false` for left and `true` for right. -/
def BinaryMessageTree.encode (T : BinaryMessageTree) : T.Path → List Bool :=
  match T with
  | .leaf => fun _ => []
  | .fork l r => fun t => match t with
      | .inl p => false :: l.encode p
      | .inr p => true :: r.encode p

/-- The partial decoder that accepts precisely bit strings ending at a leaf of the binary
message tree. -/
def BinaryMessageTree.decode (T : BinaryMessageTree) : List Bool → Option T.Path :=
  match T with
  | .leaf => fun bits => match bits with
      | [] => some ()
      | _ :: _ => none
  | .fork l r => fun bits => match bits with
      | [] => none
      | false :: bs => (l.decode bs).map Sum.inl
      | true :: bs => (r.decode bs).map Sum.inr

/-- A one-way guessing protocol with input-dependent Alice instruments producing tree paths and
message-dependent Bob instruments guessing the input. -/
structure OneWayGuessingProtocol (X : Type) [Fintype X] (T : BinaryMessageTree)
    (A E B F : ℕ) where
  alice : X → Instrument T.Path A E
  bob : T.Path → Instrument X B F

/-- Bob's unnormalized conditional state after Alice applies the branch selected by the input
and message. -/
noncomputable def OneWayGuessingProtocol.bobState {X : Type} [Fintype X]
    {T : BinaryMessageTree} {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (x : X) (t : T.Path) : Operator B :=
  partialTraceFirst (tensorLeft ((P.alice x).branch t) σ)

/-- The prior-weighted sum of correct-guess probabilities over inputs and message-tree paths. -/
noncomputable def OneWayGuessingProtocol.success {X : Type} [Fintype X]
    {T : BinaryMessageTree} {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (prior : X → ℝ) : ℝ :=
  ∑ x, ∑ t, prior x * instrumentProb (P.bob t) (P.bobState σ x t) x

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
