/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation
open Matrix
open scoped Classical

def subsetRotationFrameCorrected {N : ℕ} (S : List (Fin N)) (target : Fin N)
    (works : List (Fin N)) : Prop :=
  S.Nodup ∧ works.Nodup ∧ S.length-1 ≤ works.length ∧
    (∀ w∈S,w≠target) ∧ (∀ w∈works,w≠target) ∧
    (∀ w∈S,∀ u∈works,w≠u)

def subsetActiveWorks {N : ℕ} (S works : List (Fin N)) : List (Fin N) :=
  works.take (S.length-1)

def subsetAndLadderCorrected {N : ℕ} (S works : List (Fin N)) : List (ReflectionGate N) :=
  match S,subsetActiveWorks S works with
  | c0::c1::cs,w::ws=>toffoliLocalSteps c0 c1 w++subsetAndFold w cs ws
  | _,_=>[]

def subsetFlagWireCorrected {N : ℕ} (S : List (Fin N)) (target : Fin N) (works : List (Fin N)) : Fin N :=
  match S with
  | []=>target
  | [c]=>c
  | _=> (subsetActiveWorks S works).getLastD target

def subsetRotationStepsCorrected {N : ℕ} (S : List (Fin N)) (target : Fin N)
    (works : List (Fin N)) (θ : ℝ) : List (ReflectionGate N) :=
  match S with
  | []=>[.inl (target,qubitEulerRotation θ)]
  | _=>subsetAndLadderCorrected S works++
    multiKnownPairSteps (subsetFlagWireCorrected S target works) target ⟨0,0,θ,0⟩++
    reflectionAdjoint (subsetAndLadderCorrected S works)

def figTwoRotationStepsCorrected {N : ℕ} (target : Fin N) (works : List (Fin N))
    (terms : List (List (Fin N) × ℝ)) : List (ReflectionGate N) :=
  terms.flatMap fun p=>subsetRotationStepsCorrected p.1 target works p.2

theorem subsetActiveWorks_length {N : ℕ} (S ws : List (Fin N)) (h : S.length-1 ≤ ws.length) :
    (subsetActiveWorks S ws).length=S.length-1 := by simp [subsetActiveWorks,List.length_take,Nat.min_eq_left h]

theorem subsetAndFold_length {N : ℕ} (f : Fin N) (cs ws : List (Fin N)) (h : cs.length=ws.length) :
    (subsetAndFold f cs ws).length=15*cs.length := by
  induction cs generalizing f ws with
  | nil=>cases ws <;> simp [subsetAndFold] at h ⊢
  | cons c cs ih=>
    cases ws with
    | nil=>simp at h
    | cons w ws=>
      have hh : cs.length=ws.length := by simpa using! h
      simp only [subsetAndFold,List.length_append,toffoliLocalSteps_length,ih w ws hh,List.length_cons]
      omega

theorem subsetAndLadderCorrected_length {N : ℕ} (S ws : List (Fin N))
    (h : S.length-1 ≤ ws.length) :
    (subsetAndLadderCorrected S ws).length=15*(S.length-1) := by
  cases S with
  | nil=>simp [subsetAndLadderCorrected]
  | cons a S=>cases S with
    | nil=>simp [subsetAndLadderCorrected]
    | cons b cs=>
      have hh:=subsetActiveWorks_length (a::b::cs) ws h
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil=>simp [hw] at hh
      | cons w ww=>
        have hlen : cs.length=ww.length := by simp only [hw,List.length_cons] at hh;omega
        simp only [subsetAndLadderCorrected,hw,List.length_append,toffoliLocalSteps_length,
          subsetAndFold_length w cs ww hlen,List.length_cons]
        omega

theorem subsetAndFold_legal {N : ℕ} (cs ws : List (Fin N)) (f : Fin N)
    (hdis : ∀ c∈cs,∀ w∈ws,c≠w) (hwn : ws.Nodup)
    (hf : ∀ v,v∈cs ∨ v∈ws → f≠v) : reflectionLegal (subsetAndFold f cs ws) := by
  induction cs generalizing ws f with
  | nil=>cases ws <;> simp [subsetAndFold,reflectionLegal]
  | cons c cs ih=>
    cases ws with
    | nil=>simp [subsetAndFold,reflectionLegal]
    | cons w ws=>
      have hcw : c≠w := hdis c (by simp) w (by simp)
      have hfc : f≠c := hf c (Or.inl (by simp))
      have hfw : f≠w := hf w (Or.inr (by simp))
      have hdis' : ∀ u∈cs,∀ v∈ws,u≠v :=
          fun u hu v hv=>hdis u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)
      have hwn' : ws.Nodup := (List.nodup_cons.mp hwn).2
      have hwf : ∀ v,v∈cs ∨ v∈ws → w≠v := by
        intro v hv
        rcases hv with hv|hv
        · exact Ne.symm (hdis v (List.mem_cons_of_mem _ hv) w (by simp))
        · exact fun he=>(List.nodup_cons.mp hwn).1 (he ▸ hv)
      intro g hg
      rcases List.mem_append.mp hg with hg|hg
      · exact toffoliLocalSteps_legal f c w hfc hfw hcw g hg
      · exact ih ws w hdis' hwn' hwf g hg

theorem subsetFoldBasis_preserves {N : ℕ} (cs ws : List (Fin N)) (f : Fin N) (x : Reg N)
    (t : Fin N) (ht : t∉ws) : subsetFoldBasis f cs ws x t=x t := by
  induction cs generalizing ws f x with
  | nil=>cases ws <;> rfl
  | cons c cs ih=>cases ws with
    | nil=>rfl
    | cons w ws=>
      have hp : t≠w ∧ t∉ws := by simpa using! ht
      have htw : t≠w := hp.1
      have htail : t∉ws := fun hh=>ht (List.mem_cons_of_mem _ hh)
      rw [subsetFoldBasis,ih ws w _ htail,subsetStageBasis,Function.update_of_ne htw]

theorem subsetStageBasis_update {N : ℕ} (x : Reg N) (a c w t : Fin N) (b : Bool)
    (ha : a≠t) (hc : c≠t) (hw : w≠t) :
    subsetStageBasis (Function.update x t b) a c w=Function.update (subsetStageBasis x a c w) t b := by
  unfold subsetStageBasis
  rw [Function.update_of_ne hw,Function.update_of_ne ha,Function.update_of_ne hc,
    Function.update_comm hw]

theorem subsetFoldBasis_update {N : ℕ} (cs ws : List (Fin N)) (f t : Fin N) (x : Reg N) (b : Bool)
    (hf : f≠t) (hcs : ∀ c∈cs,c≠t) (hws : ∀ w∈ws,w≠t) :
    subsetFoldBasis f cs ws (Function.update x t b)=Function.update (subsetFoldBasis f cs ws x) t b := by
  induction cs generalizing ws f x with
  | nil=>cases ws <;> rfl
  | cons c cs ih=>cases ws with
    | nil=>rfl
    | cons w ws=>
      rw [subsetFoldBasis,subsetStageBasis_update x f c w t b hf (hcs c (by simp)) (hws w (by simp))]
      exact ih ws w _ (hws w (by simp))
        (fun u hu=>hcs u (List.mem_cons_of_mem _ hu))
        (fun u hu=>hws u (List.mem_cons_of_mem _ hu))

def subsetLadderBasisCorrected {N : ℕ} (S ws : List (Fin N)) (x : Reg N) : Reg N :=
  match S,subsetActiveWorks S ws with
  | a::b::cs,w::ww=>subsetFoldBasis w cs ww (subsetStageBasis x a b w)
  | _,_=>x

theorem subsetActiveWorks_frame {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) :
    (subsetActiveWorks S ws).Nodup ∧
    (∀ w∈subsetActiveWorks S ws,w≠t) ∧
    (∀ c∈S,∀ w∈subsetActiveWorks S ws,c≠w) := by
  refine ⟨h.2.1.take,?_,?_⟩
  · intro w hw
    exact h.2.2.2.2.1 w (List.mem_of_mem_take hw)
  · intro c hc w hw
    exact h.2.2.2.2.2 c hc w (List.mem_of_mem_take hw)

private theorem subsetWorkLast {α : Type} (w : α) (ws : List α) (t : α) :
    (w::ws).getLastD t=ws.getLastD w := by cases ws <;> simp [List.getLastD]

theorem subsetAndLadderCorrected_transport {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) :
    reflectionLegal (subsetAndLadderCorrected S ws) ∧
    ∀ x : Reg N,Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (subsetAndLadderCorrected S ws)) (Ket x)=Ket (subsetLadderBasisCorrected S ws x) := by
  cases S with
  | nil=>simp [subsetAndLadderCorrected,subsetLadderBasisCorrected,reflectionLegal,reflectionCompile]
  | cons a S=>cases S with
    | nil=>simp [subsetAndLadderCorrected,subsetLadderBasisCorrected,reflectionLegal,reflectionCompile]
    | cons b cs=>
      have ha:=subsetActiveWorks_frame (a::b::cs) ws t h
      have hlen:=subsetActiveWorks_length (a::b::cs) ws h.2.2.1
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil=>simp [hw] at hlen
      | cons w ww=>
        rw [hw] at ha
        have hab : a≠b := by
          intro he
          exact (List.nodup_cons.mp h.1).1 (he ▸ (by simp : b∈b::cs))
        have haw : a≠w := ha.2.2 a (by simp) w (by simp)
        have hbw : b≠w := ha.2.2 b (by simp) w (by simp)
        have hd : ∀ c∈cs,∀ u∈ww,c≠u := fun c hc u hu=>ha.2.2 c (by simp [hc]) u (by simp [hu])
        have hn : ww.Nodup := (List.nodup_cons.mp ha.1).2
        have hf : ∀ u,u∈cs ∨ u∈ww → w≠u := by
          intro u hu
          rcases hu with hu|hu
          · exact Ne.symm (ha.2.2 u (by simp [hu]) w (by simp))
          · exact fun he=>(List.nodup_cons.mp ha.1).1 (he ▸ hu)
        constructor
        · intro g hg
          simp only [subsetAndLadderCorrected,hw,List.mem_append] at hg
          rcases hg with hg|hg
          · exact toffoliLocalSteps_legal a b w hab haw hbw g hg
          · exact subsetAndFold_legal cs ww w hd hn hf g hg
        · intro x
          simp only [subsetAndLadderCorrected,hw,subsetLadderBasisCorrected,reflectionCompile_append,run_append]
          rw [(local_toffoli_fifteen_exact N a b w hab haw hbw).2.2 x]
          exact subsetAndFold_basis_transport cs ww hd hn w hf _

theorem subsetLadderBasisCorrected_update {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (x : Reg N) (b : Bool) :
    subsetLadderBasisCorrected S ws (Function.update x t b)=
      Function.update (subsetLadderBasisCorrected S ws x) t b := by
  cases S with
  | nil=>rfl
  | cons a S=>cases S with
    | nil=>rfl
    | cons c cs=>
      have ha:=subsetActiveWorks_frame (a::c::cs) ws t h
      cases hw : subsetActiveWorks (a::c::cs) ws with
      | nil=>simp [subsetLadderBasisCorrected,hw]
      | cons w ww=>
        rw [hw] at ha
        simp only [subsetLadderBasisCorrected,hw]
        rw [subsetStageBasis_update x a c w t b (h.2.2.2.1 a (by simp))
          (h.2.2.2.1 c (by simp)) (ha.2.1 w (by simp))]
        exact subsetFoldBasis_update cs ww w t _ b (ha.2.1 w (by simp))
          (fun u hu=>h.2.2.2.1 u (by simp [hu])) (fun u hu=>ha.2.1 u (by simp [hu]))

theorem subsetLadderBasisCorrected_flag {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (hne : S≠[])
    (x : Reg N) (hc : ∀ w∈ws,x w=false) :
    subsetLadderBasisCorrected S ws x (subsetFlagWireCorrected S t ws)=subsetControlTrue S x := by
  cases S with
  | nil=>simp at hne
  | cons a S=>cases S with
    | nil=>simp [subsetLadderBasisCorrected,subsetFlagWireCorrected,subsetControlTrue]
    | cons b cs=>
      have ha:=subsetActiveWorks_frame (a::b::cs) ws t h
      have hlen:=subsetActiveWorks_length (a::b::cs) ws h.2.2.1
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil=>simp [hw] at hlen
      | cons w ww=>
        rw [hw] at ha
        have hl : cs.length=ww.length := by simp only [hw,List.length_cons] at hlen;omega
        have hd : ∀ c∈cs,∀ u∈ww,c≠u := fun c hc u hu=>ha.2.2 c (by simp [hc]) u (by simp [hu])
        have hn : ww.Nodup := (List.nodup_cons.mp ha.1).2
        have hclean : ∀ u∈ww,subsetStageBasis x a b w u=false := by
          intro u hu
          have huw : u≠w := fun he=>(List.nodup_cons.mp ha.1).1 (he ▸ hu)
          rw [subsetStageBasis,Function.update_of_ne huw]
          have huA : u∈subsetActiveWorks (a::b::cs) ws := by rw [hw];simp [hu]
          exact hc u (List.mem_of_mem_take huA)
        have hstage : subsetStageBasis x a b w w=(x a && x b) := by
          have hwA : w∈subsetActiveWorks (a::b::cs) ws := by rw [hw];simp
          rw [subsetStageBasis,Function.update_self,hc w (List.mem_of_mem_take hwA),Bool.false_xor]
        have hcontrol (u : Fin N) (hu : u∈cs) : subsetStageBasis x a b w u=x u := by
          exact Function.update_of_ne (ha.2.2 u (by simp [hu]) w (by simp)) _ _
        simp only [subsetLadderBasisCorrected,subsetFlagWireCorrected,hw,subsetWorkLast]
        rw [subsetAndFold_basis_last cs ww hl hd hn _ w hclean,hstage]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq,Bool.and_eq_true,subsetControlTrue,List.all_eq_true,List.mem_cons]
        constructor
        · rintro ⟨⟨hxA,hxB⟩,hs⟩ u (rfl|rfl|hu)
          · exact hxA
          · exact hxB
          · rw [← hcontrol u hu];exact hs u hu
        · intro hs
          exact ⟨⟨hs a (by simp),hs b (by simp)⟩,fun u hu=>by rw [hcontrol u hu];exact hs u (by simp [hu])⟩

theorem subsetFlagWireCorrected_ne {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (hne : S≠[]) : subsetFlagWireCorrected S t ws≠t := by
  cases S with
  | nil=>simp at hne
  | cons a S=>cases S with
    | nil=>exact h.2.2.2.1 a (by simp)
    | cons b cs=>
      have ha:=subsetActiveWorks_frame (a::b::cs) ws t h
      have hl:=subsetActiveWorks_length (a::b::cs) ws h.2.2.1
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil=>simp [hw] at hl
      | cons w ww=>
        have hm : (subsetActiveWorks (a::b::cs) ws).getLastD t∈subsetActiveWorks (a::b::cs) ws := by
          rw [hw,subsetWorkLast]
          exact List.getLastD_mem_cons
        exact ha.2.1 _ hm

theorem subsetAndLadderCorrected_fiber {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (subsetAndLadderCorrected S ws))
      (multiWireState t x φ)=multiWireState t (subsetLadderBasisCorrected S ws x) φ := by
  have hb (b : Bool) : ApplyGate (reflectionProgramMatrix (subsetAndLadderCorrected S ws))
      (Ket (Function.update x t b))=Ket (Function.update (subsetLadderBasisCorrected S ws x) t b) := by
    rw [← run_reflectionCompile,(subsetAndLadderCorrected_transport S ws t h).2,
      subsetLadderBasisCorrected_update S ws t h x b]
  rw [run_reflectionCompile]
  simp only [multiWireState,reflectionApplyGate_add,reflectionApplyGate_smul,hb]

theorem subsetAndLadderCorrected_uncompute {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint (subsetAndLadderCorrected S ws)))
      (multiWireState t (subsetLadderBasisCorrected S ws x) φ)=multiWireState t x φ := by
  have hl:=(subsetAndLadderCorrected_transport S ws t h).1
  rw [← subsetAndLadderCorrected_fiber S ws t h x φ,run_reflectionCompile,run_reflectionCompile,
    reflectionAdjoint_matrix _ hl,ApplyGate,ApplyGate,Matrix.mulVec_mulVec]
  have hu:=reflectionProgramMatrix_unitary (subsetAndLadderCorrected S ws) hl
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] at hu
  rw [hu,Matrix.one_mulVec]

private theorem subsetPairSteps_length {N : ℕ} (c t : Fin N) (p : KnownQubitAngles) :
    (multiKnownPairSteps c t p).length=6 := by rfl

theorem subsetRotationStepsCorrected_legal_cost {N : ℕ} (S ws : List (Fin N)) (t : Fin N) (θ : ℝ)
    (h : subsetRotationFrameCorrected S t ws) :
    reflectionLegal (subsetRotationStepsCorrected S t ws θ) ∧
    (subsetRotationStepsCorrected S t ws θ).length=multiKnownCost S.length := by
  cases S with
  | nil=>
    constructor
    · intro g hg
      simp only [subsetRotationStepsCorrected,List.mem_singleton] at hg
      subst g
      exact qubitEulerRotation_unitary θ
    · simp [subsetRotationStepsCorrected,multiKnownCost]
  | cons a cs=>
    have hn : a::cs≠[] := by simp
    have hl:=(subsetAndLadderCorrected_transport (a::cs) ws t h).1
    have hp:=multiKnownPairSteps_legal (subsetFlagWireCorrected (a::cs) t ws) t
      (subsetFlagWireCorrected_ne (a::cs) ws t h hn) ⟨0,0,θ,0⟩
    constructor
    · intro g hg
      have hm : g∈subsetAndLadderCorrected (a::cs) ws ∨
          g∈multiKnownPairSteps (subsetFlagWireCorrected (a::cs) t ws) t ⟨0,0,θ,0⟩ ∨
          g∈reflectionAdjoint (subsetAndLadderCorrected (a::cs) ws) := by
        simpa only [subsetRotationStepsCorrected,List.mem_append,or_assoc] using! hg
      rcases hm with hg|hg|hg
      · exact hl g hg
      · exact hp g hg
      · exact reflectionAdjoint_legal _ hl g hg
    · simp only [subsetRotationStepsCorrected,List.length_append,reflectionAdjoint_length,
        subsetPairSteps_length,subsetAndLadderCorrected_length _ _ h.2.2.1,multiKnownCost,List.length_cons]
      split_ifs <;> first | contradiction | omega

theorem subset_rotation_actual_table_semantics_cost_corrected :
    ∀ (N : ℕ) (S : List (Fin N)) (target : Fin N) (works : List (Fin N)) (θ : ℝ),
    subsetRotationFrameCorrected S target works →
    reflectionLegal (subsetRotationStepsCorrected S target works θ) ∧
    (subsetRotationStepsCorrected S target works θ).length=multiKnownCost S.length ∧
    ∀ (x : Reg N) (φ : QState Bool),(∀ w∈works,x w=false) →
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (subsetRotationStepsCorrected S target works θ))
      (multiWireState target x φ)=
      multiWireState target x (ApplyGate (if subsetControlTrue S x then qubitEulerRotation θ else 1) φ) := by
  intro N S t ws θ h
  refine ⟨(subsetRotationStepsCorrected_legal_cost S ws t θ h).1,
    (subsetRotationStepsCorrected_legal_cost S ws t θ h).2,?_⟩
  intro x φ hc
  cases S with
  | nil=>
    simpa [subsetRotationStepsCorrected,reflectionCompile,Run,subsetControlTrue] using!
        multiWireState_single t x (qubitEulerRotation θ) φ
  | cons a cs=>
    have hn : a::cs≠[] := by simp
    simp only [subsetRotationStepsCorrected,reflectionCompile_append,run_append]
    rw [subsetAndLadderCorrected_fiber (a::cs) ws t h x φ,
      multiKnownPairSteps_action _ _ (subsetFlagWireCorrected_ne (a::cs) ws t h hn),
      subsetLadderBasisCorrected_flag (a::cs) ws t h hn x hc,
      subsetAndLadderCorrected_uncompute (a::cs) ws t h x]
    have hp : knownQubitUnitary ⟨0,0,θ,0⟩=qubitEulerRotation θ := by
      simp [knownQubitUnitary,qubitEulerPhase_zero]
    rw [hp]

theorem figtwo_rotation_program_semantics_and_cost_corrected :
    ∀ (N : ℕ) (target : Fin N) (works : List (Fin N)) (terms : List (List (Fin N) × ℝ)),
    (∀ p∈terms,subsetRotationFrameCorrected p.1 target works) →
    reflectionLegal (figTwoRotationStepsCorrected target works terms) ∧
    (figTwoRotationStepsCorrected target works terms).length=(terms.map fun p=>multiKnownCost p.1.length).sum ∧
    ∀ (x : Reg N) (φ : QState Bool),(∀ w∈works,x w=false) →
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (figTwoRotationStepsCorrected target works terms))
      (multiWireState target x φ)=multiWireState target x (ApplyGate (qubitEulerRotation (subsetRotationAngle terms x)) φ) := by
  intro N t ws terms
  induction terms with
  | nil=>intro _;simp [figTwoRotationStepsCorrected,reflectionLegal,reflectionCompile,subsetRotationAngle,qubitEulerRotation_zero]
  | cons p terms ih=>
    intro h
    have hp:=subset_rotation_actual_table_semantics_cost_corrected N p.1 t ws p.2 (h p (by simp))
    have ht:=ih (fun q hq=>h q (List.mem_cons_of_mem _ hq))
    have hword : figTwoRotationStepsCorrected t ws (p::terms)=
        subsetRotationStepsCorrected p.1 t ws p.2++figTwoRotationStepsCorrected t ws terms := rfl
    constructor
    · intro g hg
      rw [hword] at hg
      exact (List.mem_append.mp hg).elim (hp.1 g) (ht.1 g)
    constructor
    · rw [hword,List.length_append,hp.2.1,ht.2.1]
      rfl
    · intro x φ hc
      rw [hword,reflectionCompile_append,run_append,hp.2.2 x φ hc,ht.2.2 x _ hc]
      rw [ApplyGate,ApplyGate,Matrix.mulVec_mulVec]
      by_cases hf : subsetControlTrue p.1 x
      · simp [hf,ApplyGate,qubitEulerRotation_mul,subsetRotationAngle,add_comm]
      · simp [hf,ApplyGate,subsetRotationAngle]

end Qatlib.Concepts.RiskEstimation.PolyRotation
