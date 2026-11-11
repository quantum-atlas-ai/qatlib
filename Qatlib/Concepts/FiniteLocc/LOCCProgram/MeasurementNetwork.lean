/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# A teleportation measurement network

This module gives an executable staged model of qubit teleportation with an arbitrary reference
system, following the protocol of [BennettEtAl1993Teleportation]. `Physical`, `Action`, and
`step` describe allocation, preparation, measurement, communication, correction, and discard,
while `Receipt` records resource use.

The completed branches preserve the input up to the factor one quarter, and summing outcomes
recovers the input. Explicit tensor factorizations identify the prepared resource and consumed
registers; execution histories establish auxiliary-space and pair-inventory properties and
connect the runtime to `FiniteNetwork`.

## Main statements

* `run_reference`: each outcome produces one quarter of the reference-extended input with
  `completedReceipt`.
* `consumed_pair_factorization`: the measured registers factor from the teleported input.
* `history_inventory`: execution respects the prepared-pair inventory.
* `frontier1`: collects branch semantics, resource factorization, peak auxiliary use, and
  program well-formedness.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork
open Qatlib Matrix
open scoped Classical BigOperators Kronecker
set_option autoImplicit false
noncomputable section

/-- The pair of binary measurement outcomes used by the qubit teleportation protocol. -/
abbrev Outcome := Fin 2×Fin 2
/-- Operators on a qubit together with an `R`-dimensional reference system. -/
abbrev Joint (R : ℕ) := Matrix (Fin 2×Fin R) (Fin 2×Fin R) ℂ
/-- Operators on the three-qubit protocol register together with an `R`-dimensional reference
system. -/
abbrev Full (R : ℕ) := Matrix (Fin 8×Fin R) (Fin 8×Fin R) ℂ

/-- Lists the Hadamard and controlled-addition gates that prepare the qubit teleportation
resource. -/
def prepareGates : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditHbB 2),
   relabelGate (quditRegisterEquiv 2) (quditSUMbcB 2)]

/-- Lists the inverse controlled-addition and inverse Hadamard gates used before Alice's
measurement. -/
def decodeGates : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditSUMabInvB 2),
   relabelGate (quditRegisterEquiv 2) (quditHaInvB 2)]

/-- Lists Bob's outcome-dependent X and Z correction gates on the three-qubit register. -/
def correctionGates (o : Outcome) : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditBobXB 2 o),
   relabelGate (quditRegisterEquiv 2) (quditBobZB 2 o)]

/-- Projects onto computational-basis register states with Alice's two-qubit label equal to the
specified outcome. -/
def aliceProjector (o : Outcome) : Operator 8 :=
  Projector (Finset.univ.filter (fun r => quditAliceLabel 2 r=(quditOutcomeEquiv 2) o))

/-- Conjugates a full operator by a protocol gate tensored with the identity on the reference
system. -/
def act {R : ℕ} (U : Operator 8) (A : Full R) : Full R :=
  (TensorGate U (1:Operator R))*A*(TensorGate U (1:Operator R))ᴴ

/-- Applies a list of protocol gates in order by reference-extended conjugation. -/
def applyGates {R : ℕ} : List (Operator 8)→Full R→Full R
  | [],A => A
  | U::us,A => applyGates us (act U A)

/-- Embeds the input and reference operator into the full register using the initial protocol
frame. -/
def allocate {R : ℕ} (X : Joint R) : Full R :=
  let F := quditInitialFrame 2 ⊗ₖ (1:Operator R)
  F*X*Fᴴ

/-- Relabels the full register and takes the partial trace over Alice's registers. -/
def discard {R : ℕ} (A : Full R) : Joint R :=
  Matrix.traceLeft (relabelGate (quditReferenceEquiv 2 R) A)

/-- The stages of the teleportation runtime, carrying the current operator and any measurement
record or transmitted word. -/
inductive Physical (R : ℕ) where
  | input (X : Joint R)
  | allocated (A : Full R)
  | prepared (A : Full R)
  | released (A : Full R)
  | decoded (A : Full R)
  | measured (A : Full R) (record : Outcome)
  | sent (A : Full R) (wire : List Bool)
  | corrected (A : Full R)
  | finished (X : Joint R)

/-- The allowed instruction forms for allocation, preparation, release, decoding, measurement,
transmission, correction, and discard. -/
inductive Action where
  | allocate | prepare | release | decode | measure (record : Outcome) | transmit | correct | discard

/-- Records prepared and consumed pairs, gates, measurements, classical bits, and live and peak
auxiliary counts. -/
structure Receipt where
  prepared : ℕ := 0
  consumed : ℕ := 0
  gates : ℕ := 0
  measurements : ℕ := 0
  bits : ℕ := 0
  liveAux : ℕ := 0
  peakAux : ℕ := 0
  deriving DecidableEq

/-- A physical protocol stage paired with its accumulated resource receipt. -/
abbrev Runtime (R : ℕ) := Physical R×Receipt

/-- Executes one instruction when the physical stage permits it, updating the operator and
resource receipt and returning `none` for invalid transitions. -/
def step {R : ℕ} : Action→Runtime R→Option (Runtime R)
  | .allocate,(.input X,r) =>
      some (.allocated (allocate X),{r with liveAux:=r.liveAux+2,peakAux:=max r.peakAux (r.liveAux+2)})
  | .prepare,(.allocated A,r) =>
      some (.prepared (applyGates prepareGates A),
        {r with prepared:=r.prepared+1,gates:=r.gates+prepareGates.length})
  | .release,(.prepared A,r) => some (.released A,r)
  | .decode,(.released A,r) =>
      some (.decoded (applyGates decodeGates A),{r with gates:=r.gates+decodeGates.length})
  | .measure o,(.decoded A,r) =>
      some (.measured (act (aliceProjector o) A) o,
        {r with consumed:=r.consumed+1,measurements:=r.measurements+1})
  | .transmit,(.measured A o,r) =>
      let word := quditMessage 2 1 o
      some (.sent A word,{r with bits:=r.bits+word.length})
  | .correct,(.sent A word,r) =>
      match quditDecodeMessage 2 1 word with
      | none => none
      | some o => some (.corrected (applyGates (correctionGates o) A),
          {r with gates:=r.gates+(correctionGates o).length})
  | .discard,(.corrected A,r) =>
      some (.finished (discard A),{r with liveAux:=r.liveAux-2})
  | _,_ => none

/-- Executes a list of actions, propagating failure from any invalid transition. -/
def execute {R : ℕ} : List Action→Runtime R→Option (Runtime R)
  | [],s => some s
  | a::as,s => (step a s).bind (execute as)

/-- Lists the complete teleportation instruction sequence for a specified measurement outcome. -/
def actions (o : Outcome) : List Action :=
  [.allocate,.prepare,.release,.decode,.measure o,.transmit,.correct,.discard]

/-- Initializes the runtime with the input operator and an empty resource receipt. -/
def initial {R : ℕ} (X : Joint R) : Runtime R := (.input X,{})

/-- Executes the complete instruction sequence from the initial runtime for a specified outcome. -/
def run {R : ℕ} (X : Joint R) (o : Outcome) : Option (Runtime R) := execute (actions o) (initial X)

/-- Computes the allocated, prepared, decoded, measured, and corrected branch before discarding
Alice's registers. -/
def branchBeforeDiscard {R : ℕ} (X : Joint R) (o : Outcome) : Full R :=
  applyGates (correctionGates o)
    (act (aliceProjector o) (applyGates decodeGates (applyGates prepareGates (allocate X))))

/-- The final receipt with one prepared and consumed pair, six gates, one measurement, two
classical bits, no live auxiliaries, and peak auxiliary count two. -/
def completedReceipt : Receipt :=
  {prepared:=1,consumed:=1,gates:=6,measurements:=1,bits:=2,liveAux:=0,peakAux:=2}

/-- The generated instruction sequence terminates with the explicit branch after discard and
`completedReceipt`. -/
theorem run_generated {R : ℕ} (X : Joint R) (o : Outcome) :
    run X o=some (.finished (discard (branchBeforeDiscard X o)),completedReceipt) := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [run,actions,initial,execute,step,Option.bind_some,hd,hl,
    prepareGates,decodeGates,correctionGates,List.length_cons,List.length_nil]
  rfl

/-- Successive reference-extended conjugations by `V` and `U` equal conjugation by `U * V`. -/
theorem act_mul {R : ℕ} (U V : Operator 8) (A : Full R) :
    act U (act V A)=act (U*V) A := by
  have ht : TensorGate (U*V) (1:Operator R)=
      TensorGate U (1:Operator R)*TensorGate V (1:Operator R) := by
    rw [tensorGate_mul,Matrix.one_mul]
  simp only [act,ht,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Expresses gate action on the allocated input as conjugation by the gate composed with the
initial frame. -/
theorem act_allocate {R : ℕ} (U : Operator 8) (X : Joint R) :
    act U (allocate X)=
      ((TensorGate U (1:Operator R))*(quditInitialFrame 2⊗ₖ(1:Operator R)))*X*
        (((TensorGate U (1:Operator R))*(quditInitialFrame 2⊗ₖ(1:Operator R)))ᴴ) := by
  simp only [act,allocate,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- The explicit pre-discard branch equals conjugation of the allocated input by the
reference-extended teleportation leaf operator. -/
theorem branchBeforeDiscard_actual {R : ℕ} (X : Joint R) (o : Outcome) :
    branchBeforeDiscard X o=
      (TensorGate (quditProgramLeaf 2 o).operator (1:Operator R))*allocate X*
        (TensorGate (quditProgramLeaf 2 o).operator (1:Operator R))ᴴ := by
  simp only [branchBeforeDiscard,prepareGates,decodeGates,correctionGates,applyGates]
  rw [act_mul,act_mul,act_mul,act_mul,act_mul,act_mul]
  rw [quditProgramLeaf_operator]
  rfl

/-- Discarding the explicit branch agrees with `quditActualReferenceCore` for qubit
teleportation. -/
theorem discard_actual {R : ℕ} (X : Joint R) (o : Outcome) :
    discard (branchBeforeDiscard X o)=quditActualReferenceCore 2 R o X := by
  rw [branchBeforeDiscard_actual]
  rfl

/-- For each measurement outcome, the runtime terminates with one quarter of the input operator
and the completed receipt, including any reference system [BennettEtAl1993Teleportation]. -/
theorem run_reference {R : ℕ} (X : Joint R) (o : Outcome) :
    run X o=some (.finished (((1:ℂ)/4) • X),completedReceipt) := by
  rw [run_generated,discard_actual,quditActualReferenceCore_uniform]
  norm_num

/-- Summing the discarded branches over all measurement outcomes recovers the input operator,
including its reference system. -/
theorem forget_reference {R : ℕ} (X : Joint R) :
    (∑ o : Outcome,discard (branchBeforeDiscard X o))=X := by
  simpa only [discard_actual] using! (qudit_actual_entangled_reference_recovery 2 R X).2

/-- Applying the preparation gates to the allocated input equals conjugation by the prepared
frame tensored with the reference identity. -/
theorem preparation_actual {R : ℕ} (X : Joint R) :
    applyGates prepareGates (allocate X)=
      (quditPreparedFrame 2⊗ₖ(1:Operator R))*X*(quditPreparedFrame 2⊗ₖ(1:Operator R))ᴴ := by
  simp only [prepareGates,applyGates]
  rw [act_mul,act_allocate]
  have hf : TensorGate
      (relabelGate (quditRegisterEquiv 2) (quditSUMbcB 2)*
        relabelGate (quditRegisterEquiv 2) (quditHbB 2)) (1:Operator R)*
      (quditInitialFrame 2⊗ₖ(1:Operator R))=quditPreparedFrame 2⊗ₖ(1:Operator R) := by
    rw [← CircuitRelabel.relabelGate_mul]
    change (relabelGate (quditRegisterEquiv 2) (quditSUMbcB 2*quditHbB 2)⊗ₖ(1:Operator R))*
      (quditInitialFrame 2⊗ₖ(1:Operator R))=_
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
    rfl
  rw [hf]

/-- Defines the rectangular frame that appends the vector `ψ` to each input basis state. -/
def resourceFrame {A B : Type} [DecidableEq A] (ψ : QState B) : Matrix (A×B) A ℂ :=
  fun p j => if p.1=j then ψ p.2 else 0

/-- Conjugation by `resourceFrame ψ` equals tensoring the input operator with the outer product
of `ψ`. -/
theorem resourceFrame_tensor {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ψ : QState B) (X : Matrix A A ℂ) :
    resourceFrame (A:=A) ψ*X*(resourceFrame (A:=A) ψ)ᴴ=TensorGate X (outerProduct ψ) := by
  ext ⟨a,b⟩ ⟨a',b'⟩
  simp [resourceFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,
    TensorGate,Matrix.kroneckerMap_apply,outerProduct_apply,apply_ite]
  ring

/-- Reorders the prepared register and reference indices into an input-reference index and a
resource-pair index. -/
def preparedReferenceEquiv (R : ℕ) : Fin 8×Fin R≃(Fin 2×Fin R)×Outcome where
  toFun p := let t := (quditRegisterEquiv 2).symm p.1
             ((t.1.1,p.2),(t.1.2,t.2))
  invFun p := ((quditRegisterEquiv 2) ((p.1.1,p.2.1),p.2.2),p.1.2)
  left_inv p := by rcases p with ⟨q,r⟩; simp
  right_inv p := by rcases p with ⟨⟨a,r⟩,⟨b,c⟩⟩; simp

/-- After reindexing rows, the reference-extended prepared frame is the frame appending the
teleportation resource vector. -/
theorem preparation_rows (R : ℕ) :
    (quditPreparedFrame 2⊗ₖ(1:Operator R)).submatrix (preparedReferenceEquiv R).symm id=
      resourceFrame (A:=Fin 2×Fin R) (quditResource 2) := by
  ext ⟨⟨a,r⟩,⟨b,c⟩⟩ ⟨j,s⟩
  change quditPreparedFrame 2 ((quditRegisterEquiv 2) ((a,b),c)) j*(1:Operator R) r s=_
  rw [quditPreparedFrame_resource]
  by_cases ha : a=j <;> by_cases hr : r=s <;>
    simp [resourceFrame,Matrix.one_apply,ha,hr]

/-- After relabeling, the prepared state factors as the input-reference operator tensored with
the resource outer product. -/
theorem preparation_resource {R : ℕ} (X : Joint R) :
    relabelGate (preparedReferenceEquiv R) (applyGates prepareGates (allocate X))=
      TensorGate X (outerProduct (quditResource 2)) := by
  rw [preparation_actual,qudit_relabel_frame_sandwich,preparation_rows,resourceFrame_tensor]

/-- Conjugation by a fixed-label frame tensors the input operator with the corresponding
computational-basis projector. -/
theorem fixedFrame_tensor {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (o : A) (X : Matrix B B ℂ) :
    quditFixedFrame (B:=B) o*X*(quditFixedFrame (B:=B) o)ᴴ=
      TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket o)) X := by
  ext ⟨a,b⟩ ⟨a',b'⟩
  by_cases ha : a=o <;> by_cases ha' : a'=o <;>
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,quditFixedFrame,
      TensorGate,Matrix.kroneckerMap_apply,outerProduct_apply,Qatlib.Foundations.PureStateMath.Ket,ha,ha']

/-- After relabeling, each corrected pre-discard branch is one quarter of the measured-outcome
projector tensored with the input-reference operator. -/
theorem consumed_pair_factorization {R : ℕ} (X : Joint R) (o : Outcome) :
    relabelGate (quditReferenceEquiv 2 R) (branchBeforeDiscard X o)=
      ((1:ℂ)/4) • TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket o)) X := by
  let F := quditInitialFrame 2⊗ₖ(1:Operator R)
  let L := TensorGate (quditProgramLeaf 2 o).operator (1:Operator R)
  have he : L*(F*X*Fᴴ)*Lᴴ=(L*F)*X*(L*F)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hf : L*F=((1:ℂ)/2) • (quditOutcomeFrame 2 o⊗ₖ(1:Operator R)) := by
    dsimp [L,F,TensorGate]
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,quditProgramLeaf_frame,Matrix.smul_kronecker]
    norm_num
  rw [branchBeforeDiscard_actual]
  change relabelGate (quditReferenceEquiv 2 R) (L*(F*X*Fᴴ)*Lᴴ)=_
  rw [he,hf,qudit_relabel_frame_sandwich]
  simp only [Matrix.submatrix_smul,Pi.smul_apply,quditOutcomeFrame_reference_rows]
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [fixedFrame_tensor]
  norm_num

/-- Returns the input wire at the initial stage, the output wire at the finished stage, and all
three wires at intermediate stages. -/
def liveWires {R : ℕ} : Physical R→Finset (Fin 3)
  | .input _ => {0}
  | .finished _ => {2}
  | _ => Finset.univ

/-- Counts the live protocol wires beyond one distinguished system wire. -/
def auxiliaryCount {R : ℕ} (s : Physical R) : ℕ := (liveWires s).card-1

/-- Executes an action list while retaining the initial runtime and every subsequent runtime,
returning `none` on failure. -/
def history {R : ℕ} : List Action→Runtime R→Option (List (Runtime R))
  | [],s => some [s]
  | a::as,s => (step a s).bind (fun t => (history as t).map (fun ts => s::ts))

/-- The full execution history has auxiliary counts and recorded live-auxiliary counts both
equal to `[0,2,2,2,2,2,2,2,0]`. -/
theorem history_auxiliary {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      ts.map (fun s => auxiliaryCount s.1)=[0,2,2,2,2,2,2,2,0] ∧
      ts.map (fun s => s.2.liveAux)=[0,2,2,2,2,2,2,2,0] := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [actions,initial,history,step,Option.bind_some,Option.map_some,hd,hl]
  refine ⟨_,rfl,?_,?_⟩ <;>
    norm_num [List.map,auxiliaryCount,liveWires,prepareGates,decodeGates,correctionGates]

/-- The maximum auxiliary count along a complete execution history equals the peak count in
`completedReceipt`. -/
theorem peak_from_history {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      (ts.map (fun s => auxiliaryCount s.1)).foldl max 0=completedReceipt.peakAux := by
  obtain ⟨ts,ht,hq,_⟩ := history_auxiliary X o
  refine ⟨ts,ht,?_⟩
  rw [hq]
  rfl

/-- A measured stage rejects another measurement, preparation, and direct correction. -/
theorem no_pair_reuse {R : ℕ} (A : Full R) (r : Receipt) (o p : Outcome) :
    step (.measure p) (.measured A o,r)=none ∧
      step .prepare (.measured A o,r)=none ∧
      step .correct (.measured A o,r)=none := by
  exact ⟨rfl,rfl,rfl⟩

/-- A finished stage rejects measurement, correction, and allocation. -/
theorem no_use_after_discard {R : ℕ} (X : Joint R) (r : Receipt) (o : Outcome) :
    step (.measure o) (.finished X,r)=none ∧
      step .correct (.finished X,r)=none ∧ step .allocate (.finished X,r)=none := by
  exact ⟨rfl,rfl,rfl⟩

/-- Defines the finite qubit network consisting of one teleportation step followed by
termination. -/
def network : FiniteNetwork 2 2 := .teleport inferInstance 1 (by decide) (fun _ => .done 2)
/-- Builds the transcript of the single-step teleportation network from a measurement outcome. -/
def transcript (o : Outcome) : network.Transcript := ⟨o,()⟩

/-- The network transcript uses one fresh qubit pair, six matrix gates, one macro measurement,
and two classical bits. -/
theorem network_resources (o : Outcome) :
    network.resources (transcript o)=
      {freshPairDimensions:=[2],bellPairsPrepared:=1,matrixGates:=6,
        macroMeasurements:=1,classicalBits:=2} := by
  simpa only [network,transcript,FiniteNetwork.resources,FiniteNetwork.events,eventResources,
    Nat.add_zero,List.length_nil,List.length_cons] using!
    teleport_node_resources (n:=2) 1 (by decide) (fun _ => .done 2) o ()

/-- The discarded physical branch equals the reference extension of the corresponding
finite-network branch. -/
theorem reference_network_bridge {R : ℕ} (X : Joint R) (o : Outcome) :
    discard (branchBeforeDiscard X o)=tensorLeft (networkBranch network (transcript o)) X := by
  have hn : ∀ρ : Operator 2,networkBranch network (transcript o) ρ=((1:ℂ)/4) • ρ := by
    intro ρ
    change (quditCorrectedInstrument 2).branch o ρ=_
    rw [quditCorrectedInstrument_branch]
    norm_num
  have he := tensorLeft_eq_smul ((1:ℂ)/4) hn X
  rw [discard_actual,quditActualReferenceCore_uniform]
  norm_num at he ⊢
  exact he.symm

/-- Returns one for prepared, released, and decoded stages, and zero for all other stages. -/
def availablePair {R : ℕ} : Physical R→ℕ
  | .prepared _ | .released _ | .decoded _ => 1
  | _ => 0

/-- A complete history has the stated available-pair counts, and every runtime in it has
consumed at most as many pairs as it has prepared. -/
theorem history_inventory {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      ts.map (fun s => availablePair s.1)=[0,0,1,1,1,0,0,0,0] ∧
      (∀s∈ts,s.2.consumed ≤ s.2.prepared) := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [actions,initial,history,step,Option.bind_some,Option.map_some,hd,hl]
  refine ⟨_,rfl,?_,?_⟩ <;>
    norm_num [List.map,availablePair,prepareGates,decodeGates,correctionGates]

/-- Expresses Alice's decoding gates and Bob's conditional corrections as tensor products
supported on their respective local registers. -/
theorem online_local_gate_forms :
    quditSUMabInvB 2=TensorGate (quditSUM 2)ᴴ (1:Operator 2) ∧
      quditHaInvB 2=TensorGate (TensorGate (QFTMatrix 2)ᴴ (1:Operator 2)) (1:Operator 2) ∧
      (∀o : Outcome,
        quditBobXB 2 o=TensorGate (1:Matrix Outcome Outcome ℂ)
          (quditX 2 (-((ZMod.finEquiv 2) o.2))) ∧
        quditBobZB 2 o=TensorGate (1:Matrix Outcome Outcome ℂ)
          (quditZ 2 ((ZMod.finEquiv 2) o.1))) :=
  ⟨rfl,rfl,fun _ => ⟨rfl,rfl⟩⟩

/-- Alice's measurement projector is the outcome projector tensored with the identity on Bob's
qubit. -/
theorem alice_projector_local (o : Outcome) :
    quditAliceProjectorB 2 o=TensorGate (Projector {o}) (1:Operator 2) := by
  unfold quditAliceProjectorB TensorGate Projector
  rw [← Matrix.diagonal_one,Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext p
  simp

/-- Collects the reference-preserving branch formula, prepared and consumed register
factorizations, outcome-sum identity, peak auxiliary count, and observed well-formedness of
the qubit teleportation program [BennettEtAl1993Teleportation]. -/
theorem frontier1 {R : ℕ} (X : Joint R) (o : Outcome) :
    run X o=some (.finished (((1:ℂ)/4) • X),completedReceipt) ∧
      relabelGate (preparedReferenceEquiv R) (applyGates prepareGates (allocate X))=
        TensorGate X (outerProduct (quditResource 2)) ∧
      relabelGate (quditReferenceEquiv 2 R) (branchBeforeDiscard X o)=
        ((1:ℂ)/4) • TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket o)) X ∧
      (∑p : Outcome,discard (branchBeforeDiscard X p))=X ∧
      (∃ts,history (actions o) (initial X)=some ts ∧
        (ts.map (fun s => auxiliaryCount s.1)).foldl max 0=completedReceipt.peakAux) ∧
      observedWellFormed (quditProgram 2) :=
  ⟨run_reference X o,preparation_resource X,consumed_pair_factorization X o,
    forget_reference X,peak_from_history X o,quditProgram_wellFormed 2⟩

end
end Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork
