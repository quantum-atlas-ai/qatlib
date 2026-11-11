/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyStat
import Qatlib.Concepts.GramQueryCore.ModelSemantics.AlphabetWordSemanticsQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.PhaseDetectionQuan

/-!
# Assembly of alphabet oracle walk words

Constructs an isometric encoding of the witness walk into an alphabet query space. A controlled
product of the keep and complement reflections is realized by a legal source word containing
exactly two oracle calls, following the state conversion construction of [LeeEtAl2011].

Adjoint words, frame extensions, and permutation identities support substitution of this walk
implementation into arbitrary legal words with at most twice their original query count.

## Main statements

* `sourceAlphabetWalkMacro`: realizes the controlled walk with two alphabet queries.
* `sourceWordCompile`: substitutes an implementation through an isometric frame.
* `alphabetPhaseWordAssembly`: proves the alphabet word assembly specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

/-- A unitary on the domain of an isometric frame extends to a unitary on its ambient space,
intertwining through the frame. -/
theorem sourceExtendFrameUnitary {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (F : Matrix S T ℂ) (hF : Fᴴ*F=1)
    (U : Matrix T T ℂ) (hU : U ∈ Matrix.unitaryGroup T ℂ) :
    ∃ G : Matrix S S ℂ, G ∈ Matrix.unitaryGroup S ℂ ∧ G*F=F*U := by
  have hu : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  apply gram_equal_actual_unitary_transport S T F (F*U)
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Fᴴ F,hF,Matrix.one_mul,hu]

/-- Takes the adjoint of a gate letter and reverses the direction of an oracle letter. -/
def sourceAdjointLetter {S : Type} : Matrix S S ℂ ⊕ Bool → Matrix S S ℂ ⊕ Bool
  | .inl U => .inl Uᴴ
  | .inr b => .inr (!b)

/-- The adjoint source word, obtained by reversing its letters and taking each letter's adjoint. -/
def sourceAdjointWord {S : Type} (C : SourceWord S) : SourceWord S :=
  C.reverse.map sourceAdjointLetter

/-- The matrix of `C ++ D` is the matrix of `D` multiplied by the matrix of `C`. -/
theorem sourceWordMatrix_append {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C D : SourceWord S) :
    sourceWordMatrix O (C++D)=sourceWordMatrix O D*sourceWordMatrix O C := by
  simp [sourceWordMatrix,List.map_append,List.reverse_append,List.prod_append]

/-- Concatenating source words adds their oracle call counts. -/
theorem sourceWordCalls_append {S : Type} (C D : SourceWord S) :
    sourceWordCalls (C++D)=sourceWordCalls C+sourceWordCalls D := by
  simp [sourceWordCalls]

/-- The concatenation of two legal source words is legal. -/
theorem sourceWordLegal_append {S : Type} [Fintype S] [DecidableEq S]
    (C D : SourceWord S) (hC : sourceWordLegal C) (hD : sourceWordLegal D) :
    sourceWordLegal (C++D) := by
  intro s hs
  rcases List.mem_append.mp hs with hs|hs
  · exact hC s hs
  · exact hD s hs

/-- Taking the adjoint word preserves the oracle call count. -/
theorem sourceAdjointWord_calls {S : Type} (C : SourceWord S) :
    sourceWordCalls (sourceAdjointWord C)=sourceWordCalls C := by
  unfold sourceWordCalls sourceAdjointWord
  rw [List.countP_map]
  calc
    _ = List.countP (fun s => match s with | .inl _ => false | .inr _ => true) C.reverse := by
      apply List.countP_congr
      intro s _
      cases s <;> simp [sourceAdjointLetter]
    _ = _ := List.countP_reverse

/-- Evaluation of the adjoint word gives the conjugate transpose of the original word's matrix. -/
theorem sourceAdjointWord_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) :
    sourceWordMatrix O (sourceAdjointWord C)=(sourceWordMatrix O C)ᴴ := by
  unfold sourceWordMatrix sourceAdjointWord
  simp only [List.map_map,Function.comp_def,← List.map_reverse,List.reverse_reverse]
  induction C with
  | nil => simp
  | cons s C ih =>
    simp only [List.map_cons,List.prod_cons,List.reverse_cons,List.map_append,List.prod_append,
      List.prod_cons,List.map_nil,List.prod_nil,mul_one,Matrix.conjTranspose_mul,ih]
    cases s with
    | inl U => simp [sourceAdjointLetter]
    | inr b => cases b <;> simp [sourceAdjointLetter]

/-- Taking the adjoint of a legal source word preserves legality. -/
theorem sourceAdjointWord_legal {S : Type} [Fintype S] [DecidableEq S]
    (C : SourceWord S) (hC : sourceWordLegal C) : sourceWordLegal (sourceAdjointWord C) := by
  intro s hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  have hh := hC t (List.mem_reverse.mp ht)
  cases t with
  | inl U => simpa only [sourceAdjointLetter,Matrix.star_eq_conjTranspose] using! Unitary.star_mem hh
  | inr b => trivial

/-- An intertwining relation between unitary matrices through a frame also holds for their
adjoints. -/
theorem sourceFrame_adjoint {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (F : Matrix S T ℂ) (A : Matrix S S ℂ) (U : Matrix T T ℂ)
    (hA : A ∈ Matrix.unitaryGroup S ℂ) (hU : U ∈ Matrix.unitaryGroup T ℂ)
    (h : A*F=F*U) : Aᴴ*F=F*Uᴴ := by
  have hAA : Aᴴ*A=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hA.1
  have hUU : U*Uᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  calc
    Aᴴ*F = Aᴴ*(F*(U*Uᴴ)) := by rw [hUU,Matrix.mul_one]
    _ = Aᴴ*((F*U)*Uᴴ) := by rw [Matrix.mul_assoc]
    _ = Aᴴ*((A*F)*Uᴴ) := by rw [h]
    _ = F*Uᴴ := by simp [← Matrix.mul_assoc,hAA]

/-- Adding a Boolean control and a clock register of size `2^b` to a unitary matrix preserves
unitarity. -/
theorem sourceControlledU_unitary {H : Type} [Fintype H] [DecidableEq H]
    (b : ℕ) [DecidableEq ((Bool × H) × Fin (2^b))]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    sourceControlledU (2^b) U ∈ Matrix.unitaryGroup _ ℂ := by
  let e := Equiv.prodComm ((Bool × H)) (Fin (2^b))
  have he : sourceControlledU (2^b) U=relabelGate e.symm
      (TensorGate (1 : Matrix (Fin (2^b)) (Fin (2^b)) ℂ) (controlOracle U)) := by
    ext p t
    simp [sourceControlledU,relabelGate,e,TensorGate,controlOracle,Qatlib.Concepts.BlockEncoding.LCU.select,Matrix.one_apply]
    split_ifs <;> simp_all [Matrix.one_apply]
  rw [he]
  exact (relabelGate_mem_unitaryGroup _ _).mpr
    (tensorGate_unitary (Matrix.unitaryGroup _ ℂ).one_mem (controlOracle_unitary hU))

/-- The walk basis permutation that adds the input symbol to each query sector's alphabet
register and fixes the other registers. -/
def sourceWalkShift {X H : Type} {n q m b : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    ((Bool × SourceGeometry n q m H) × Fin (2^b)) ≃
      ((Bool × SourceGeometry n q m H) × Fin (2^b)) where
  toFun p := ((p.1.1,match p.1.2 with
    | .inl t => .inl t
    | .inr (j,a,k) => .inr (j,a+input x j,k)),p.2)
  invFun p := ((p.1.1,match p.1.2 with
    | .inl t => .inl t
    | .inr (j,a,k) => .inr (j,a-input x j,k)),p.2)
  left_inv p := by rcases p with ⟨⟨c,t⟩,z⟩; cases t <;> simp
  right_inv p := by rcases p with ⟨⟨c,t⟩,z⟩; cases t <;> simp

/-- The auxiliary labels for the walk encoding, consisting of a state or witness label together
with a clock value. -/
abbrev SourceWalkAux (H : Type) (m b : ℕ) := ((Bool × H) ⊕ Fin m) × Fin (2^b)

/-- Encodes walk auxiliary labels into a finite register with one additional position. -/
def sourceWalkAuxCode (H : Type) [Fintype H] (m b : ℕ) :
    SourceWalkAux H m b → Fin (Fintype.card (SourceWalkAux H m b)+1) :=
  fun t => ((Fintype.equivFin (SourceWalkAux H m b)) t).castSucc

/-- The finite encoding `sourceWalkAuxCode` is injective. -/
theorem sourceWalkAuxCode_injective (H : Type) [Fintype H] (m b : ℕ) :
    Function.Injective (sourceWalkAuxCode H m b) := by
  intro t z h
  apply (Fintype.equivFin _).injective
  have hv := congrArg (fun i : Fin (Fintype.card (SourceWalkAux H m b)+1) => i.val) h
  exact Fin.ext hv

/-- Encodes walk basis labels into the padded alphabet source space using a chosen payload basis
element. -/
def sourceWalkBasisCode {H : Type} [Fintype H] (n q m b : ℕ) (h0 : H) :
    ((Bool × SourceGeometry n q m H) × Fin (2^b)) →
    SourceSpace n q H (Fintype.card (SourceWalkAux H m b)+1) := fun p =>
  match p.1.2 with
  | .inl t => ((⟨n,by omega⟩,0),((p.1.1,h0),sourceWalkAuxCode H m b (.inl t,p.2)))
  | .inr (j,a,k) => ((j.castSucc,a),((p.1.1,h0),sourceWalkAuxCode H m b (.inr k,p.2)))

/-- The alphabet vector centered at `s` is the translate of the vector centered at zero. -/
theorem sourceMu_translate (q : ℕ) (a s : Fin (q+1)) :
    sourceMu q s a=sourceMu q 0 (a-s) := by
  simp [sourceMu,sub_eq_zero]

/-- The walk basis encoding into the alphabet source space is injective. -/
theorem sourceWalkBasisCode_injective {H : Type} [Fintype H]
    (n q m b : ℕ) (h0 : H) : Function.Injective (sourceWalkBasisCode n q m b h0) := by
  intro p t he
  rcases p with ⟨⟨c,p⟩,z⟩
  rcases t with ⟨⟨d,t⟩,w⟩
  have hc := congrArg (fun v => v.2.1.1) he
  have ha := congrArg (fun v => v.1.1.val) he
  have hb := congrArg (fun v => v.1.2) he
  have hu := congrArg (fun v => v.2.2) he
  cases p with
  | inl p =>
    cases t with
    | inl t =>
      have hx := sourceWalkAuxCode_injective H m b hu
      have hp := congrArg (fun v => v.1) hx
      have hz := congrArg (fun v => v.2) hx
      (try dsimp only at hz)
      simp only [Sum.inl.injEq] at hp
      simp only [sourceWalkBasisCode] at hc
      subst c; subst p; subst z
      rfl
    | inr t =>
      rcases t with ⟨j,a,k⟩
      simp only [sourceWalkBasisCode,Fin.val_castSucc] at ha
      omega
  | inr p =>
    rcases p with ⟨j,a,k⟩
    cases t with
    | inl t =>
      simp only [sourceWalkBasisCode,Fin.val_castSucc] at ha
      omega
    | inr t =>
      rcases t with ⟨l,s,h⟩
      have hx := sourceWalkAuxCode_injective H m b hu
      have hk := congrArg (fun v => v.1) hx
      have hz := congrArg (fun v => v.2) hx
      (try dsimp only at hz)
      simp only [Sum.inr.injEq] at hk
      simp only [sourceWalkBasisCode,Fin.val_castSucc] at ha hc hb
      have hj : j=l := Fin.ext ha
      subst c; subst j; subst a; subst k; subst z
      rfl

/-- The matrix whose column at `t` is the standard basis vector indexed by `e t`. -/
def sourceBasisFrame {S T : Type} [DecidableEq S] (e : T → S) : Matrix S T ℂ :=
  fun s t => if s=e t then 1 else 0

/-- The standard basis frame associated with an injective map is an isometry. -/
theorem sourceBasisFrame_isometry {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : T → S) (he : Function.Injective e) :
    (sourceBasisFrame e)ᴴ*sourceBasisFrame e=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,sourceBasisFrame]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply,he.eq_iff]
  · intro s _ hs
    simp [hs]
  · simp

/-- A basis frame intertwines permutations that agree along its defining basis map. -/
theorem sourceBasisFrame_permutation {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : T → S) (σ : S → S) (τ : T ≃ T)
    (h : ∀ t, σ (e t)=e (τ t)) :
    permMatrix σ*sourceBasisFrame e=sourceBasisFrame e*permMatrix τ := by
  ext s t
  have hl : (permMatrix σ*sourceBasisFrame e) s t=if s=σ (e t) then 1 else 0 := by
    simp only [Matrix.mul_apply,sourceBasisFrame,permMatrix,Matrix.of_apply]
    rw [Finset.sum_eq_single (e t)]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have hr : (sourceBasisFrame e*permMatrix τ) s t=if s=e (τ t) then 1 else 0 := by
    simp only [Matrix.mul_apply,sourceBasisFrame,permMatrix,Matrix.of_apply]
    rw [Finset.sum_eq_single (τ t)]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  rw [hl,hr,h]

/-- The alphabet oracle acts on the encoded walk frame as the walk shift permutation. -/
theorem sourceWalkFrame_oracle {X H : Type} [Fintype H] [DecidableEq H] {n q m b : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) (h0 : H) :
    sourceAlphabetOracle input x*sourceBasisFrame (sourceWalkBasisCode n q m b h0)=
      sourceBasisFrame (sourceWalkBasisCode n q m b h0)*permMatrix (sourceWalkShift (m:=m) (b:=b) input x) := by
  apply sourceBasisFrame_permutation
  intro t
  rcases t with ⟨⟨c,t⟩,z⟩
  cases t with
  | inl t => simp [sourceWalkBasisCode,sourceWalkShift,sourcePaddedSymbol]
  | inr t =>
    rcases t with ⟨j,a,k⟩
    simp [sourceWalkBasisCode,sourceWalkShift,sourcePaddedSymbol,j.isLt]

/-- Conjugation by a permutation matrix is the corresponding relabeling of a gate. -/
theorem sourcePermutation_conjugate {T : Type} [Fintype T] [DecidableEq T]
    (e : T ≃ T) (U : Matrix T T ℂ) :
    permMatrix e*U*(permMatrix e)ᴴ=relabelGate e U := by
  ext i j
  simp only [Matrix.mul_apply,permMatrix,Matrix.of_apply,Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · simp only [e.apply_symm_apply,ite_true,star_one,mul_one]
    rw [Finset.sum_eq_single (e.symm i)]
    · simp [relabelGate]
    · intro t _ ht
      have he : i≠e t := by intro h; apply ht; exact ((e.symm_apply_eq).mpr h).symm
      simp [he]
    · simp
  · intro t _ ht
    have he : j≠e t := by intro h; apply ht; exact ((e.symm_apply_eq).mpr h).symm
    simp [he]
  · simp

/-- The geometry permutation that adds the input symbol in each query sector and fixes the state
sector. -/
def sourceGeometryShift {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    SourceGeometry n q m H ≃ SourceGeometry n q m H where
  toFun p := match p with
    | .inl t => .inl t
    | .inr (j,a,k) => .inr (j,a+input x j,k)
  invFun p := match p with
    | .inl t => .inl t
    | .inr (j,a,k) => .inr (j,a-input x j,k)
  left_inv p := by cases p <;> simp
  right_inv p := by cases p <;> simp

/-- Relabeling the zero-input keep matrix by the input-dependent geometry shift gives the keep
matrix for that input. -/
theorem sourceKeep_translation {X H : Type} [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    relabelGate (sourceGeometryShift (H:=H) (m:=m) input x)
      (sourceKeep (fun (_ : Unit) (_ : Fin n) => (0 : Fin (q+1))) ())=sourceKeep input x := by
  ext p t
  cases p with
  | inl p => cases t <;> simp [relabelGate,sourceGeometryShift,sourceKeep]
  | inr p =>
    rcases p with ⟨j,a,k⟩
    cases t with
    | inl t => simp [relabelGate,sourceGeometryShift,sourceKeep]
    | inr t =>
      rcases t with ⟨l,b,h⟩
      by_cases hj : j=l
      · subst l
        simp [relabelGate,sourceGeometryShift,sourceKeep,← sourceMu_translate]
      · simp [relabelGate,sourceGeometryShift,sourceKeep,hj]

/-- Relabeling the state register commutes with forming the controlled matrix and its clock
extension. -/
theorem sourceControlledU_relabel {H : Type} [Fintype H] [DecidableEq H]
    (e : H ≃ H) (r : ℕ) (U : Matrix H H ℂ) :
    relabelGate ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Bool) e) (Equiv.refl (Fin r))))
      (sourceControlledU r U)=sourceControlledU r (relabelGate e U) := by
  ext p t
  simp [relabelGate,sourceControlledU]

/-- Relabeling a reflection matrix gives the reflection about the relabeled matrix. -/
theorem sourceReflection_relabel {H : Type} [Fintype H] [DecidableEq H]
    (e : H ≃ H) (P : Matrix H H ℂ) :
    relabelGate e (ReflectionAbout P)=ReflectionAbout (relabelGate e P) := by
  ext i j
  simp [relabelGate,ReflectionAbout,Matrix.one_apply,e.symm.injective.eq_iff]

/-- Conjugating the controlled zero-input keep reflection by the walk shift gives the controlled
keep reflection for the input. -/
theorem sourceWalkKeep_conjugate {X H : Type} [Fintype H] [DecidableEq H] {n q m b : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    permMatrix (sourceWalkShift (H:=H) (m:=m) (b:=b) input x) *
      sourceControlledU (2^b) (ReflectionAbout
        (sourceKeep (H:=H) (m:=m) (fun (_ : Unit) (_ : Fin n) => (0 : Fin (q+1))) ())) *
      (permMatrix (sourceWalkShift input x))ᴴ =
      sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x)) := by
  rw [sourcePermutation_conjugate]
  change relabelGate ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Bool)
    (sourceGeometryShift input x)) (Equiv.refl (Fin (2^b))))) _=_
  rw [sourceControlledU_relabel,sourceReflection_relabel,sourceKeep_translation]

/-- The controlled clock extension preserves matrix multiplication. -/
theorem sourceControlledU_mul {H : Type} [Fintype H] [DecidableEq H]
    (r : ℕ) (U V : Matrix H H ℂ) :
    sourceControlledU r (U*V)=sourceControlledU r U*sourceControlledU r V := by
  let e := Equiv.prodComm (Bool × H) (Fin r)
  have he (A : Matrix H H ℂ) : sourceControlledU r A=relabelGate e.symm
      (TensorGate (1 : Matrix (Fin r) (Fin r) ℂ) (controlOracle A)) := by
    ext p t
    simp [sourceControlledU,relabelGate,e,TensorGate,controlOracle,Qatlib.Concepts.BlockEncoding.LCU.select,Matrix.one_apply]
    split_ifs <;> simp_all [Matrix.one_apply]
  rw [he,he,he,← CircuitRelabel.relabelGate_mul,tensorGate_mul]
  congr 1
  rw [Matrix.one_mul]
  congr 1
  unfold controlOracle
  ext ⟨c,i⟩ ⟨d,j⟩
  cases c <;> cases d <;> simp
      [Qatlib.Concepts.BlockEncoding.LCU.select,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply]

/-- An isometric implementation using at most two queries per oracle call compiles any legal
source word with at most twice its call count and preserves the action through the frame. -/
theorem sourceWordCompile {X S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (F : Matrix S T ℂ) (hF : Fᴴ*F=1)
    (O : X → Matrix S S ℂ) (U : X → Matrix T T ℂ)
    (hO : ∀ x, O x ∈ Matrix.unitaryGroup S ℂ)
    (hU : ∀ x, U x ∈ Matrix.unitaryGroup T ℂ)
    (Q : SourceWord S) (hQ : sourceWordLegal Q) (hq : sourceWordCalls Q≤2)
    (hact : ∀ x, sourceWordMatrix (O x) Q*F=F*U x)
    (C : SourceWord T) (hC : sourceWordLegal C) :
    ∃ D : SourceWord S, sourceWordLegal D ∧ sourceWordCalls D≤2*sourceWordCalls C ∧
      ∀ x, sourceWordMatrix (O x) D*F=F*sourceWordMatrix (U x) C := by
  have step (s : Matrix T T ℂ ⊕ Bool)
      (hs : match s with | .inl A => A ∈ Matrix.unitaryGroup T ℂ | .inr _ => True) :
      ∃ R : SourceWord S, sourceWordLegal R ∧ sourceWordCalls R≤2*sourceWordCalls [s] ∧
        ∀ x, sourceWordMatrix (O x) R*F=F*sourceWordMatrix (U x) [s] := by
    cases s with
    | inl A =>
      obtain ⟨G,hG,hGF⟩ := sourceExtendFrameUnitary F hF A hs
      refine ⟨[.inl G],?_,by simp [sourceWordCalls],?_⟩
      · intro s hs
        simp only [List.mem_singleton] at hs
        subst s
        exact hG
      · intro x
        simpa only [sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,
          List.prod_cons,List.prod_nil,Matrix.mul_one] using! hGF
    | inr b =>
      cases b with
      | false =>
        refine ⟨Q,hQ,by simpa [sourceWordCalls] using! hq,?_⟩
        intro x
        simpa [sourceWordMatrix] using! hact x
      | true =>
        refine ⟨sourceAdjointWord Q,sourceAdjointWord_legal Q hQ,?_,?_⟩
        · rw [sourceAdjointWord_calls]
          simpa [sourceWordCalls] using! hq
        · intro x
          rw [sourceAdjointWord_matrix]
          simpa [sourceWordMatrix] using! sourceFrame_adjoint F
            (sourceWordMatrix (O x) Q) (U x) (sourceWordMatrix_unitary _ (hO x) Q hQ)
              (hU x) (hact x)
  induction C with
  | nil => exact ⟨[],by simp [sourceWordLegal],by simp [sourceWordCalls],by simp [sourceWordMatrix]⟩
  | cons s C ih =>
    have hs := hC s List.mem_cons_self
    have ht : sourceWordLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    obtain ⟨R,hR,hcalls,hRact⟩ := step s hs
    obtain ⟨D,hD,hcount,hDact⟩ := ih ht
    refine ⟨R++D,sourceWordLegal_append R D hR hD,?_,?_⟩
    · rw [sourceWordCalls_append]
      have he : sourceWordCalls (s::C)=sourceWordCalls [s]+sourceWordCalls C :=
        sourceWordCalls_append [s] C
      rw [he]
      omega
    · intro x
      rw [sourceWordMatrix_append,Matrix.mul_assoc,hRact,
        ← Matrix.mul_assoc,hDact,Matrix.mul_assoc]
      have he : sourceWordMatrix (U x) (s::C)=
          sourceWordMatrix (U x) C*sourceWordMatrix (U x) [s] :=
        sourceWordMatrix_append (U x) [s] C
      rw [he]

/-- The controlled product of the keep and complement reflections has a legal alphabet oracle
implementation with exactly two calls through an isometric frame. -/
theorem sourceAlphabetWalkMacro {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H]
    (n q m b : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (hq : 0<q) :
    ∃ (r : ℕ) (_hr : 0<r)
      (F : Matrix (SourceSpace n q H r) ((Bool × SourceGeometry n q m H) × Fin (2^b)) ℂ)
      (Q : SourceWord (SourceSpace n q H r)),
      Fᴴ*F=1 ∧ sourceWordLegal Q ∧ sourceWordCalls Q=2 ∧
      ∀ x, sourceWordMatrix (sourceAlphabetOracle input x) Q*F=
        F*sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x)*
          ReflectionAbout (sourceComplement input ρ σ u W ε)) := by
  let h0 : H := Classical.choice inferInstance
  let r := Fintype.card (SourceWalkAux H m b)+1
  let F := sourceBasisFrame (sourceWalkBasisCode n q m b h0)
  have hF : Fᴴ*F=1 := sourceBasisFrame_isometry _ (sourceWalkBasisCode_injective n q m b h0)
  let P0 := sourceKeep (H:=H) (m:=m) (fun (_ : Unit) (_ : Fin n) => (0 : Fin (q+1))) ()
  let L := sourceComplement input ρ σ u W ε
  have hP0 : IsOrthogonalProjector P0 := sourceKeep_isOrthogonalProjector _ () hq
  have hL : IsOrthogonalProjector L := (sourceComplement_public input ρ σ u W ε).1
  let K0 := sourceControlledU (2^b) (ReflectionAbout P0)
  let L0 := sourceControlledU (2^b) (ReflectionAbout L)
  have hK0 : K0 ∈ Matrix.unitaryGroup _ ℂ :=
      sourceControlledU_unitary b _ (reflectionAbout_unitary hP0)
  have hL0 : L0 ∈ Matrix.unitaryGroup _ ℂ :=
      sourceControlledU_unitary b _ (reflectionAbout_unitary hL)
  obtain ⟨KGate,hKGate,hK⟩ := sourceExtendFrameUnitary F hF K0 hK0
  obtain ⟨LGate,hLGate,hG⟩ := sourceExtendFrameUnitary F hF L0 hL0
  let Q : SourceWord (SourceSpace n q H r) := [.inl LGate,.inr true,.inl KGate,.inr false]
  refine ⟨r,by dsimp [r]; omega,F,Q,hF,?_,by rfl,?_⟩
  · intro s hs
    simp only [Q,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl
    · exact hLGate
    · trivial
    · exact hKGate
    · trivial
  · intro x
    let O := sourceAlphabetOracle (W:=((Bool × H) × Fin r)) input x
    let B := permMatrix (sourceWalkShift (H:=H) (m:=m) (b:=b) input x)
    have hO : O ∈ Matrix.unitaryGroup _ ℂ := sourceAlphabetOracle_unitary input x
    have hB : B ∈ Matrix.unitaryGroup _ ℂ :=
        permMatrix_unitary_of_injective (sourceWalkShift input x).injective
    have hOF : O*F=F*B := sourceWalkFrame_oracle input x h0
    have hOaF : Oᴴ*F=F*Bᴴ := sourceFrame_adjoint F O B hO hB hOF
    have hsem : sourceWordMatrix O Q=O*KGate*Oᴴ*LGate := by
      simp [sourceWordMatrix,Q,Matrix.mul_assoc]
    rw [sourceControlledU_mul]
    change sourceWordMatrix O Q*F=F*(sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x))*L0)
    rw [hsem]
    calc
      (O*KGate*Oᴴ*LGate)*F = O*(KGate*(Oᴴ*(LGate*F))) := by simp only [Matrix.mul_assoc]
      _ = O*(KGate*(Oᴴ*(F*L0))) := by rw [hG]
      _ = O*(KGate*((Oᴴ*F)*L0)) := by rw [Matrix.mul_assoc]
      _ = O*(KGate*((F*Bᴴ)*L0)) := by rw [hOaF]
      _ = O*((KGate*F)*(Bᴴ*L0)) := by simp only [Matrix.mul_assoc]
      _ = O*((F*K0)*(Bᴴ*L0)) := by rw [hK]
      _ = (O*F)*(K0*Bᴴ*L0) := by simp only [Matrix.mul_assoc]
      _ = (F*B)*(K0*Bᴴ*L0) := by rw [hOF]
      _ = F*((B*K0*Bᴴ)*L0) := by simp only [Matrix.mul_assoc]
      _ = F*(sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x))*L0) := by
        rw [sourceWalkKeep_conjugate]

/-- Proves the alphabet phase word assembly specification, supplying the walk compilation used
in [Lee et al., Theorem 4.1][LeeEtAl2011]. -/
theorem alphabetPhaseWordAssembly : AlphabetPhaseWordAssembly := by
  intro X H _ _ _ _ _ n q m b input ρ σ u W ε hq C hC
  obtain ⟨r,hr,F,Q,hF,hQ,hcalls,hact⟩ := sourceAlphabetWalkMacro n q m b input ρ σ u W ε hq
  have hU (x : X) : sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x)*
      ReflectionAbout (sourceComplement input ρ σ u W ε)) ∈ Matrix.unitaryGroup _ ℂ := by
    apply sourceControlledU_unitary
    exact (Matrix.unitaryGroup _ ℂ).mul_mem
      (reflectionAbout_unitary (sourceKeep_isOrthogonalProjector input x hq))
      (reflectionAbout_unitary (sourceComplement_public input ρ σ u W ε).1)
  obtain ⟨D,hD,hcount,hsem⟩ := sourceWordCompile F hF (sourceAlphabetOracle input)
    (fun x => sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x)*
      ReflectionAbout (sourceComplement input ρ σ u W ε)))
    (sourceAlphabetOracle_unitary input) hU Q hQ (by rw [hcalls]) hact C hC
  refine ⟨r,hr,F,D,hF,hD,hcount,?_⟩
  intro x ψ
  rw [Matrix.mulVec_mulVec,hsem,← Matrix.mulVec_mulVec]

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
