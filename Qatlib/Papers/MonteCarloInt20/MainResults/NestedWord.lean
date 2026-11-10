/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedPreparation
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord

noncomputable local instance dataDecision (n M : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool) :=
  instDecidableEqProd

noncomputable local instance fullDecision (n M N : ℕ) (I : Type) [DecidableEq I] :
    DecidableEq (Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner N ((Reg n × Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn.Inner M I) × Bool)) :=
  instDecidableEqProd

inductive AccessTag where
  | inputForward | inputBackward | innerMark | outerMark | sampleHadamard | payoffRotation | fixed
  deriving DecidableEq

def reverseTag : AccessTag → AccessTag
  | .inputForward => .inputBackward
  | .inputBackward => .inputForward
  | a => a

abbrev GateWord (G : Type*) := List (AccessTag × G)

def wordEval {G : Type*} [Monoid G] : GateWord G → G
  | [] => 1
  | (_,U) :: w => wordEval w*U

theorem wordEval_append {G : Type*} [Monoid G] (u v : GateWord G) :
    wordEval (u++v)=wordEval v*wordEval u := by
  induction u with
  | nil => simp [wordEval]
  | cons a u ih => simp only [List.cons_append,wordEval,ih,mul_assoc]

def liftWord {G H : Type*} (f : G → H) (w : GateWord G) : GateWord H :=
  w.map (fun p => (p.1,f p.2))

theorem wordEval_lift {G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (w : GateWord G) :
    wordEval (liftWord f w)=f (wordEval w) := by
  induction w with
  | nil => exact f.map_one.symm
  | cons a w ih =>
    change wordEval (liftWord f w)*f a.2=f (wordEval w*a.2)
    rw [ih,map_mul]

def accessCount {G : Type*} (t : AccessTag) (w : GateWord G) : ℕ :=
  (w.map (fun p => if p.1=t then 1 else 0)).sum

theorem accessCount_append {G : Type*} (t : AccessTag) (u v : GateWord G) :
    accessCount t (u++v)=accessCount t u+accessCount t v := by
  simp [accessCount,List.map_append,List.sum_append]

theorem accessCount_lift {G H : Type*} (t : AccessTag) (f : G → H) (w : GateWord G) :
    accessCount t (liftWord f w)=accessCount t w := by
  simp [accessCount,liftWord,List.map_map,Function.comp_def]

def adjointWord {I : Type} [Fintype I] [DecidableEq I]
    (w : GateWord (Matrix I I ℂ)) : GateWord (Matrix I I ℂ) :=
  (w.map (fun p => (reverseTag p.1,p.2.conjTranspose))).reverse

theorem wordEval_adjoint {I : Type} [Fintype I] [DecidableEq I]
    (w : GateWord (Matrix I I ℂ)) : wordEval (adjointWord w)=(wordEval w).conjTranspose := by
  induction w with
  | nil => simp [adjointWord,wordEval]
  | cons a w ih =>
    simp only [adjointWord,List.map_cons,List.reverse_cons,wordEval_append,wordEval]
    rw [show wordEval (List.reverse (List.map (fun p => (reverseTag p.1,p.2.conjTranspose)) w))=
      (wordEval w).conjTranspose from ih]
    simp [Matrix.conjTranspose_mul]

theorem accessCount_adjoint {I : Type} [Fintype I] [DecidableEq I]
    (t : AccessTag) (w : GateWord (Matrix I I ℂ)) :
    accessCount t (adjointWord w)=accessCount (reverseTag t) w := by
  simp only [accessCount,adjointWord,List.map_reverse,List.sum_reverse,List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  rcases p with ⟨s,U⟩
  cases t <;> cases s <;> rfl

def selectHom {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] :
    (J → Matrix I I ℂ) →* Matrix (J × I) (J × I) ℂ where
  toFun := select
  map_one' := parallel_select_one
  map_mul' _ _ := (parallel_select_mul _ _).symm

def rightSpectatorHom {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Matrix I I ℂ →* Matrix (I × J) (I × J) ℂ where
  toFun U := TensorGate U 1
  map_one' := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hi : i=k <;> by_cases hj : j=l <;> simp [TensorGate,Matrix.one_apply,hi,hj]
  map_mul' U V := by rw [tensorGate_mul,Matrix.one_mul]

def leftSpectatorHom {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Matrix I I ℂ →* Matrix (J × I) (J × I) ℂ where
  toFun U := TensorGate 1 U
  map_one' := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hi : i=k <;> by_cases hj : j=l <;> simp [TensorGate,Matrix.one_apply,hi,hj]
  map_mul' U V := by rw [tensorGate_mul,Matrix.one_mul]

def controlHom {I : Type} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →* Matrix (Bool × I) (Bool × I) ℂ where
  toFun := controlOracle
  map_one' := controlOracle_one
  map_mul' U V := (controlOracle_mul U V).symm

def stepMatrix {I : Type} (O : Matrix I I ℂ) : Step I → Matrix I I ℂ
  | .gate U => U
  | .query => O

def innerTag {I : Type} : AEAccessStep I → AccessTag
  | .initialize | .prepareForward => .inputForward
  | .prepareBackward => .inputBackward
  | .mark => .innerMark
  | _ => .fixed

def innerFamilyWord {I J : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I)
    (w : List (AEAccessStep (Inner M I))) : GateWord (J → Matrix (Inner M I) (Inner M I) ℂ) :=
  w.map (fun a => (innerTag a,fun j => stepMatrix (aeControlledGate M (preparedMark (S j)))
    (aeAccessInstruction M (A j) i₀ a)))

theorem innerFamilyWord_eval {I J : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I)
    (w : List (AEAccessStep (Inner M I))) (j : J) :
    wordEval (innerFamilyWord M A i₀ S w) j=
      runMatrix (aeControlledGate M (preparedMark (S j))) (w.map (aeAccessInstruction M (A j) i₀)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change wordEval (innerFamilyWord M A i₀ S w) j*
      stepMatrix (aeControlledGate M (preparedMark (S j))) (aeAccessInstruction M (A j) i₀ a)=_
    rw [ih]
    cases a <;> rfl

def selectedInnerWord {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I) :
    GateWord (Matrix (J × Inner M I) (J × Inner M I) ℂ) :=
  liftWord selectHom (innerFamilyWord M A i₀ S (aeAccessWord (I:=I) M))

theorem selectedInnerWord_eval {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I) :
    wordEval (selectedInnerWord M A i₀ S)=select (fun j => innerUnitary M (A j) i₀ (S j)) := by
  rw [selectedInnerWord,wordEval_lift]
  change select (wordEval (innerFamilyWord M A i₀ S (aeAccessWord (I:=I) M)))=_
  apply congrArg select
  funext j
  exact innerFamilyWord_eval M A i₀ S (aeAccessWord M) j

theorem innerFamilyWord_counts {I J : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A : J → Matrix I I ℂ) (i₀ : I) (S : J → Finset I)
    (w : List (AEAccessStep (Inner M I))) :
    accessCount .inputForward (innerFamilyWord M A i₀ S w)=aeForwardAccesses w ∧
    accessCount .inputBackward (innerFamilyWord M A i₀ S w)=aeBackwardAccesses w := by
  constructor
  · unfold accessCount innerFamilyWord aeForwardAccesses
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    cases a <;> rfl
  · unfold accessCount innerFamilyWord aeBackwardAccesses
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    cases a <;> rfl

def preparationWord {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    GateWord (Matrix ((Reg n × Inner M I) × Bool) ((Reg n × Inner M I) × Bool) ℂ) :=
  [(.sampleHadamard,TensorGate (TensorGate (HadamardN n) 1) 1)] ++
  liftWord rightSpectatorHom (selectedInnerWord M A i₀ S) ++
  [(.payoffRotation,payoffRotation (fun p : Reg n × Inner M I => g (D*aeEstimate M p.2.1)))]

theorem preparationWord_eval {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    wordEval (preparationWord n M A i₀ S D g)=outerPreparation n M A i₀ S D g := by
  unfold preparationWord
  rw [wordEval_append,wordEval_append,wordEval_lift,selectedInnerWord_eval]
  simp only [wordEval,Matrix.one_mul]
  change (payoffRotation (fun p : Reg n × Inner M I => g (D*aeEstimate M p.2.1)))*
    (TensorGate (select (fun j => innerUnitary M (A j) i₀ (S j))) 1*
      TensorGate (TensorGate (HadamardN n) 1) 1)=_
  rw [tensorGate_mul,Matrix.one_mul]
  rfl

theorem preparationWord_counts {I : Type} [Fintype I] [DecidableEq I] (n M : ℕ) (hM : 0 < M)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    accessCount .inputForward (preparationWord n M A i₀ S D g)=M ∧
    accessCount .inputBackward (preparationWord n M A i₀ S D g)=M-1 := by
  have hc := innerFamilyWord_counts M A i₀ S (aeAccessWord (I:=I) M)
  have hf := prepared_ae_separate_access_counts (I:=I) M hM
  simp only [preparationWord,accessCount_append,accessCount_lift,selectedInnerWord]
  simp only [accessCount,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,reduceCtorEq,↓reduceIte,zero_add,add_zero]
  exact And.intro (hc.1.trans hf.1) (hc.2.trans hf.2.1)

def initializeHom {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) :
    Matrix I I ℂ →* Matrix (Inner N I) (Inner N I) ℂ :=
  leftSpectatorHom.comp leftSpectatorHom

def controlledHom {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) :
    Matrix I I ℂ →* Matrix (Inner N I) (Inner N I) ℂ :=
  leftSpectatorHom.comp controlHom

def expandOuterStep {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (i₀ : I)
    (S : Finset I) (w : GateWord (Matrix I I ℂ)) : AEAccessStep (Inner N I) →
    GateWord (Matrix (Inner N I) (Inner N I) ℂ)
  | .initialize => liftWord (initializeHom N) w
  | .prepareForward => liftWord (controlledHom N) w
  | .prepareBackward => liftWord (controlledHom N) (adjointWord w)
  | .sourceReflection => [(.fixed,stepMatrix (aeControlledGate N (preparedMark S))
      (aeAccessInstruction N (wordEval w) i₀ .sourceReflection))]
  | .mark => [(.outerMark,aeControlledGate N (preparedMark S))]
  | .fixed U => [(.fixed,U)]

theorem expandOuterStep_eval {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (i₀ : I)
    (S : Finset I) (w : GateWord (Matrix I I ℂ)) (a : AEAccessStep (Inner N I)) :
    wordEval (expandOuterStep N i₀ S w a)=stepMatrix (aeControlledGate N (preparedMark S))
      (aeAccessInstruction N (wordEval w) i₀ a) := by
  cases a with
  | «initialize» => rw [expandOuterStep,wordEval_lift]; rfl
  | prepareForward => rw [expandOuterStep,wordEval_lift]; rfl
  | prepareBackward => rw [expandOuterStep,wordEval_lift,wordEval_adjoint]; rfl
  | sourceReflection => simp [expandOuterStep,wordEval]
  | mark => simp [expandOuterStep,wordEval,aeAccessInstruction,stepMatrix]
  | fixed U => simp [expandOuterStep,wordEval,aeAccessInstruction,stepMatrix]

theorem expandedOuterWord_eval {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (i₀ : I)
    (S : Finset I) (w : GateWord (Matrix I I ℂ)) (a : List (AEAccessStep (Inner N I))) :
    wordEval (a.flatMap (expandOuterStep N i₀ S w))=
      runMatrix (aeControlledGate N (preparedMark S)) (a.map (aeAccessInstruction N (wordEval w) i₀)) := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons,wordEval_append,ih,expandOuterStep_eval]
    cases a <;> rfl

theorem expandedOuterWord_counts {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (i₀ : I)
    (S : Finset I) (w : GateWord (Matrix I I ℂ)) (a : List (AEAccessStep (Inner N I))) :
    accessCount .inputForward (a.flatMap (expandOuterStep N i₀ S w))=
      aeForwardAccesses a*accessCount .inputForward w+aeBackwardAccesses a*accessCount .inputBackward w ∧
    accessCount .inputBackward (a.flatMap (expandOuterStep N i₀ S w))=
      aeForwardAccesses a*accessCount .inputBackward w+aeBackwardAccesses a*accessCount .inputForward w := by
  induction a with
  | nil => simp [accessCount,aeForwardAccesses,aeBackwardAccesses]
  | cons a as ih =>
    cases a <;> simp only [List.flatMap_cons,accessCount_append,expandOuterStep,accessCount_lift,
      accessCount_adjoint,reverseTag,aeForwardAccesses,aeBackwardAccesses] at * <;>
      simp only [accessCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,reduceCtorEq,
        ↓reduceIte,zero_add,add_zero,Nat.add_mul,Nat.one_mul] at * <;> constructor <;> omega

def nestedWord {I : Type} [Fintype I] [DecidableEq I] (n M N : ℕ) (hM : 0 < M)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    GateWord (Matrix (Inner N ((Reg n × Inner M I) × Bool)) (Inner N ((Reg n × Inner M I) × Bool)) ℂ) :=
  (aeAccessWord (I:=((Reg n × Inner M I) × Bool)) N).flatMap (expandOuterStep N ((ZeroStr n,innerSeed M hM i₀),false)
    (Finset.univ.filter (fun p => p.2=true)) (preparationWord n M A i₀ S D g))

theorem nestedWord_source_counts {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I) (D : ℝ) (g : ℝ → ℝ) :
    accessCount .inputForward (nestedWord n M N hM A i₀ S D g)=N*M+(N-1)*(M-1) ∧
    accessCount .inputBackward (nestedWord n M N hM A i₀ S D g)=N*(M-1)+(N-1)*M := by
  have h := expandedOuterWord_counts N ((ZeroStr n,innerSeed M hM i₀),false)
    (Finset.univ.filter (fun p => p.2=true)) (preparationWord n M A i₀ S D g) (aeAccessWord N)
  have hp := preparationWord_counts n M hM A i₀ S D g
  have hn := prepared_ae_separate_access_counts (I:=((Reg n × Inner M I) × Bool)) N hN
  simpa only [nestedWord,hp.1,hp.2,hn.1,hn.2.1] using! h

end Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
