/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
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

abbrev Outcome := Fin 2×Fin 2
abbrev Joint (R : ℕ) := Matrix (Fin 2×Fin R) (Fin 2×Fin R) ℂ
abbrev Full (R : ℕ) := Matrix (Fin 8×Fin R) (Fin 8×Fin R) ℂ

def prepareGates : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditHbB 2),
   relabelGate (quditRegisterEquiv 2) (quditSUMbcB 2)]

def decodeGates : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditSUMabInvB 2),
   relabelGate (quditRegisterEquiv 2) (quditHaInvB 2)]

def correctionGates (o : Outcome) : List (Operator 8) :=
  [relabelGate (quditRegisterEquiv 2) (quditBobXB 2 o),
   relabelGate (quditRegisterEquiv 2) (quditBobZB 2 o)]

def aliceProjector (o : Outcome) : Operator 8 :=
  Projector (Finset.univ.filter (fun r => quditAliceLabel 2 r=(quditOutcomeEquiv 2) o))

def act {R : ℕ} (U : Operator 8) (A : Full R) : Full R :=
  (TensorGate U (1:Operator R))*A*(TensorGate U (1:Operator R))ᴴ

def applyGates {R : ℕ} : List (Operator 8)→Full R→Full R
  | [],A => A
  | U::us,A => applyGates us (act U A)

def allocate {R : ℕ} (X : Joint R) : Full R :=
  let F := quditInitialFrame 2 ⊗ₖ (1:Operator R)
  F*X*Fᴴ

def discard {R : ℕ} (A : Full R) : Joint R :=
  Matrix.traceLeft (relabelGate (quditReferenceEquiv 2 R) A)

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

inductive Action where
  | allocate | prepare | release | decode | measure (record : Outcome) | transmit | correct | discard

structure Receipt where
  prepared : ℕ := 0
  consumed : ℕ := 0
  gates : ℕ := 0
  measurements : ℕ := 0
  bits : ℕ := 0
  liveAux : ℕ := 0
  peakAux : ℕ := 0
  deriving DecidableEq

abbrev Runtime (R : ℕ) := Physical R×Receipt

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

def execute {R : ℕ} : List Action→Runtime R→Option (Runtime R)
  | [],s => some s
  | a::as,s => (step a s).bind (execute as)

def actions (o : Outcome) : List Action :=
  [.allocate,.prepare,.release,.decode,.measure o,.transmit,.correct,.discard]

def initial {R : ℕ} (X : Joint R) : Runtime R := (.input X,{})

def run {R : ℕ} (X : Joint R) (o : Outcome) : Option (Runtime R) := execute (actions o) (initial X)

def branchBeforeDiscard {R : ℕ} (X : Joint R) (o : Outcome) : Full R :=
  applyGates (correctionGates o)
    (act (aliceProjector o) (applyGates decodeGates (applyGates prepareGates (allocate X))))

def completedReceipt : Receipt :=
  {prepared:=1,consumed:=1,gates:=6,measurements:=1,bits:=2,liveAux:=0,peakAux:=2}

theorem run_generated {R : ℕ} (X : Joint R) (o : Outcome) :
    run X o=some (.finished (discard (branchBeforeDiscard X o)),completedReceipt) := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [run,actions,initial,execute,step,Option.bind_some,hd,hl,
    prepareGates,decodeGates,correctionGates,List.length_cons,List.length_nil]
  rfl

theorem act_mul {R : ℕ} (U V : Operator 8) (A : Full R) :
    act U (act V A)=act (U*V) A := by
  have ht : TensorGate (U*V) (1:Operator R)=
      TensorGate U (1:Operator R)*TensorGate V (1:Operator R) := by
    rw [tensorGate_mul,Matrix.one_mul]
  simp only [act,ht,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem act_allocate {R : ℕ} (U : Operator 8) (X : Joint R) :
    act U (allocate X)=
      ((TensorGate U (1:Operator R))*(quditInitialFrame 2⊗ₖ(1:Operator R)))*X*
        (((TensorGate U (1:Operator R))*(quditInitialFrame 2⊗ₖ(1:Operator R)))ᴴ) := by
  simp only [act,allocate,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem branchBeforeDiscard_actual {R : ℕ} (X : Joint R) (o : Outcome) :
    branchBeforeDiscard X o=
      (TensorGate (quditProgramLeaf 2 o).operator (1:Operator R))*allocate X*
        (TensorGate (quditProgramLeaf 2 o).operator (1:Operator R))ᴴ := by
  simp only [branchBeforeDiscard,prepareGates,decodeGates,correctionGates,applyGates]
  rw [act_mul,act_mul,act_mul,act_mul,act_mul,act_mul]
  rw [quditProgramLeaf_operator]
  rfl

theorem discard_actual {R : ℕ} (X : Joint R) (o : Outcome) :
    discard (branchBeforeDiscard X o)=quditActualReferenceCore 2 R o X := by
  rw [branchBeforeDiscard_actual]
  rfl

theorem run_reference {R : ℕ} (X : Joint R) (o : Outcome) :
    run X o=some (.finished (((1:ℂ)/4) • X),completedReceipt) := by
  rw [run_generated,discard_actual,quditActualReferenceCore_uniform]
  norm_num

theorem forget_reference {R : ℕ} (X : Joint R) :
    (∑ o : Outcome,discard (branchBeforeDiscard X o))=X := by
  simpa only [discard_actual] using! (qudit_actual_entangled_reference_recovery 2 R X).2

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

def resourceFrame {A B : Type} [DecidableEq A] (ψ : QState B) : Matrix (A×B) A ℂ :=
  fun p j => if p.1=j then ψ p.2 else 0

theorem resourceFrame_tensor {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ψ : QState B) (X : Matrix A A ℂ) :
    resourceFrame (A:=A) ψ*X*(resourceFrame (A:=A) ψ)ᴴ=TensorGate X (outerProduct ψ) := by
  ext ⟨a,b⟩ ⟨a',b'⟩
  simp [resourceFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,
    TensorGate,Matrix.kroneckerMap_apply,outerProduct_apply,apply_ite]
  ring

def preparedReferenceEquiv (R : ℕ) : Fin 8×Fin R≃(Fin 2×Fin R)×Outcome where
  toFun p := let t := (quditRegisterEquiv 2).symm p.1
             ((t.1.1,p.2),(t.1.2,t.2))
  invFun p := ((quditRegisterEquiv 2) ((p.1.1,p.2.1),p.2.2),p.1.2)
  left_inv p := by rcases p with ⟨q,r⟩; simp
  right_inv p := by rcases p with ⟨⟨a,r⟩,⟨b,c⟩⟩; simp

theorem preparation_rows (R : ℕ) :
    (quditPreparedFrame 2⊗ₖ(1:Operator R)).submatrix (preparedReferenceEquiv R).symm id=
      resourceFrame (A:=Fin 2×Fin R) (quditResource 2) := by
  ext ⟨⟨a,r⟩,⟨b,c⟩⟩ ⟨j,s⟩
  change quditPreparedFrame 2 ((quditRegisterEquiv 2) ((a,b),c)) j*(1:Operator R) r s=_
  rw [quditPreparedFrame_resource]
  by_cases ha : a=j <;> by_cases hr : r=s <;>
    simp [resourceFrame,Matrix.one_apply,ha,hr]

theorem preparation_resource {R : ℕ} (X : Joint R) :
    relabelGate (preparedReferenceEquiv R) (applyGates prepareGates (allocate X))=
      TensorGate X (outerProduct (quditResource 2)) := by
  rw [preparation_actual,qudit_relabel_frame_sandwich,preparation_rows,resourceFrame_tensor]

theorem fixedFrame_tensor {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (o : A) (X : Matrix B B ℂ) :
    quditFixedFrame (B:=B) o*X*(quditFixedFrame (B:=B) o)ᴴ=
      TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket o)) X := by
  ext ⟨a,b⟩ ⟨a',b'⟩
  by_cases ha : a=o <;> by_cases ha' : a'=o <;>
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,quditFixedFrame,
      TensorGate,Matrix.kroneckerMap_apply,outerProduct_apply,Qatlib.Foundations.PureStateMath.Ket,ha,ha']

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

def liveWires {R : ℕ} : Physical R→Finset (Fin 3)
  | .input _ => {0}
  | .finished _ => {2}
  | _ => Finset.univ

def auxiliaryCount {R : ℕ} (s : Physical R) : ℕ := (liveWires s).card-1

def history {R : ℕ} : List Action→Runtime R→Option (List (Runtime R))
  | [],s => some [s]
  | a::as,s => (step a s).bind (fun t => (history as t).map (fun ts => s::ts))

theorem history_auxiliary {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      ts.map (fun s => auxiliaryCount s.1)=[0,2,2,2,2,2,2,2,0] ∧
      ts.map (fun s => s.2.liveAux)=[0,2,2,2,2,2,2,2,0] := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [actions,initial,history,step,Option.bind_some,Option.map_some,hd,hl]
  refine ⟨_,rfl,?_,?_⟩ <;>
    norm_num [List.map,auxiliaryCount,liveWires,prepareGates,decodeGates,correctionGates]

theorem peak_from_history {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      (ts.map (fun s => auxiliaryCount s.1)).foldl max 0=completedReceipt.peakAux := by
  obtain ⟨ts,ht,hq,_⟩ := history_auxiliary X o
  refine ⟨ts,ht,?_⟩
  rw [hq]
  rfl

theorem no_pair_reuse {R : ℕ} (A : Full R) (r : Receipt) (o p : Outcome) :
    step (.measure p) (.measured A o,r)=none ∧
      step .prepare (.measured A o,r)=none ∧
      step .correct (.measured A o,r)=none := by
  exact ⟨rfl,rfl,rfl⟩

theorem no_use_after_discard {R : ℕ} (X : Joint R) (r : Receipt) (o : Outcome) :
    step (.measure o) (.finished X,r)=none ∧
      step .correct (.finished X,r)=none ∧ step .allocate (.finished X,r)=none := by
  exact ⟨rfl,rfl,rfl⟩

def network : FiniteNetwork 2 2 := .teleport inferInstance 1 (by decide) (fun _ => .done 2)
def transcript (o : Outcome) : network.Transcript := ⟨o,()⟩

theorem network_resources (o : Outcome) :
    network.resources (transcript o)=
      {freshPairDimensions:=[2],bellPairsPrepared:=1,matrixGates:=6,
        macroMeasurements:=1,classicalBits:=2} := by
  simpa only [network,transcript,FiniteNetwork.resources,FiniteNetwork.events,eventResources,
    Nat.add_zero,List.length_nil,List.length_cons] using!
    teleport_node_resources (n:=2) 1 (by decide) (fun _ => .done 2) o ()

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

def availablePair {R : ℕ} : Physical R→ℕ
  | .prepared _ | .released _ | .decoded _ => 1
  | _ => 0

theorem history_inventory {R : ℕ} (X : Joint R) (o : Outcome) :
    ∃ts, history (actions o) (initial X)=some ts ∧
      ts.map (fun s => availablePair s.1)=[0,0,1,1,1,0,0,0,0] ∧
      (∀s∈ts,s.2.consumed ≤ s.2.prepared) := by
  have hd := (quditMessage_decode 2 1 (by decide) o).2
  have hl := (quditMessage_decode 2 1 (by decide) o).1
  simp only [actions,initial,history,step,Option.bind_some,Option.map_some,hd,hl]
  refine ⟨_,rfl,?_,?_⟩ <;>
    norm_num [List.map,availablePair,prepareGates,decodeGates,correctionGates]

theorem online_local_gate_forms :
    quditSUMabInvB 2=TensorGate (quditSUM 2)ᴴ (1:Operator 2) ∧
      quditHaInvB 2=TensorGate (TensorGate (QFTMatrix 2)ᴴ (1:Operator 2)) (1:Operator 2) ∧
      (∀o : Outcome,
        quditBobXB 2 o=TensorGate (1:Matrix Outcome Outcome ℂ)
          (quditX 2 (-((ZMod.finEquiv 2) o.2))) ∧
        quditBobZB 2 o=TensorGate (1:Matrix Outcome Outcome ℂ)
          (quditZ 2 ((ZMod.finEquiv 2) o.1))) :=
  ⟨rfl,rfl,fun _ => ⟨rfl,rfl⟩⟩

theorem alice_projector_local (o : Outcome) :
    quditAliceProjectorB 2 o=TensorGate (Projector {o}) (1:Operator 2) := by
  unfold quditAliceProjectorB TensorGate Projector
  rw [← Matrix.diagonal_one,Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext p
  simp

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
