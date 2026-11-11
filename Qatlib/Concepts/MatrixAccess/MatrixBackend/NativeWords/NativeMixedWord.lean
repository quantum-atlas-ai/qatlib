/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnownWord
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
/-! Time-order native known opcodes and one original query in both
literal directions. Compilation expands 15/6/1 known instructions and
reverses physical time into the existing AdjointStep product order.
The unknown oracle is absent from the constructors/compiler. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeMixed
open Qatlib Matrix
open scoped Classical

/-- Constructors for Gate in the native mixed word model. -/
inductive Gate (N : ℕ) where
  | known : NativeKnown.Gate N → Gate N
  | forward : Gate N
  | backward : Gate N

/-- Construction for Legal in the native mixed word model. -/
def Legal {N : ℕ} : Gate N → Prop
  | .known g => NativeKnown.Legal g
  | _ => True

/-- Construction for legal Check in the native mixed word model. -/
def legalCheck {N : ℕ} : Gate N → Bool
  | .known g => NativeKnown.legalCheck g
  | _ => true

/-- The finite Boolean check accepts exactly the legal native words or opcodes. -/
theorem legalCheck_iff {N : ℕ} (g : Gate N) : legalCheck g=true ↔ Legal g := by
  cases g <;> simp [legalCheck,Legal,NativeKnown.legalCheck_iff]

/-- Construction for word Legal in the native mixed word model. -/
def wordLegal {N : ℕ} (gs : List (Gate N)) : Prop := ∀ g∈gs,Legal g

/-- Construction for matrix in the native mixed word model. -/
def matrix {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) : Gate N → Matrix (Reg N) (Reg N) ℂ
  | .known g => NativeKnown.matrix g
  | .forward => O
  | .backward => Oᴴ

/-- Construction for word Matrix in the native mixed word model. -/
def wordMatrix {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) : List (Gate N) → Matrix (Reg N) (Reg N) ℂ
  | [] => 1
  | g::gs => wordMatrix O gs * matrix O g

/-- Construction for reflection Product Word in the native mixed word model. -/
def reflectionProductWord {N : ℕ} (gs : List (ReflectionGate N)) : List (AdjointStep (Reg N)) :=
  gs.reverse.map (fun g => .gate (reflectionGateMatrix g))

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem reflectionProductWord_evaluate {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (gs : List (ReflectionGate N)) :
    evaluate O (reflectionProductWord gs)=reflectionProgramMatrix gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [reflectionProductWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,evaluate_append] at *
    rw [ih]
    simp [evaluate,instructionMatrix,reflectionProgramMatrix]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem reflectionProductWord_legal {N : ℕ} (gs : List (ReflectionGate N)) (hg : reflectionLegal gs) :
    WellFormedAdjointCircuit (reflectionProductWord gs) := by
  intro V hV
  obtain ⟨g,hmem,he⟩ := List.mem_map.mp hV
  cases he
  exact reflectionGateMatrix_mem_unitary (hg g (by simpa using hmem))

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem reflectionProductWord_counts {N : ℕ} (gs : List (ReflectionGate N)) :
    adjointQueryCount (reflectionProductWord gs)=0 ∧ adjointGateCount (reflectionProductWord gs)=gs.length := by
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    simp only [reflectionProductWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      adjointQueryCount_append,adjointGateCount_append,adjointQueryCount,adjointGateCount,List.length_cons] at *
    exact ⟨by omega,by omega⟩

/-- Construction for compile in the native mixed word model. -/
def compile {N : ℕ} : Gate N → List (AdjointStep (Reg N))
  | .known g => reflectionProductWord (NativeKnown.compile g)
  | .forward => [.forward]
  | .backward => [.backward]

/-- Construction for word Compile in the native mixed word model. -/
def wordCompile {N : ℕ} (gs : List (Gate N)) : List (AdjointStep (Reg N)) := gs.reverse.flatMap compile

/-- The finite native construction `wordCompile_append` satisfies the displayed exact coordinate or algebraic relation. -/
theorem wordCompile_append {N : ℕ} (gs hs : List (Gate N)) :
    wordCompile (gs++hs)=wordCompile hs++wordCompile gs := by
  simp [wordCompile,List.reverse_append,List.flatMap_append]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem compile_evaluate {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (g : Gate N) (hg : Legal g) :
    evaluate O (compile g)=matrix O g := by
  cases g with
  | known g => exact (reflectionProductWord_evaluate O _).trans (NativeKnown.compile_matrix g hg)
  | forward => simp [compile,evaluate,instructionMatrix,matrix]
  | backward => simp [compile,evaluate,instructionMatrix,matrix]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem compile_legal {N : ℕ} (g : Gate N) (hg : Legal g) : WellFormedAdjointCircuit (compile g) := by
  cases g with
  | known g => exact reflectionProductWord_legal _ (NativeKnown.compile_legal g hg)
  | forward => simp [compile]
  | backward => simp [compile]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem wordCompile_evaluate {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (gs : List (Gate N)) (hg : wordLegal gs) :
    evaluate O (wordCompile gs)=wordMatrix O gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ht : wordLegal gs := fun a ha => hg a (by simp [ha])
    simp only [wordCompile,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [evaluate_append,← wordCompile,ih ht,compile_evaluate O g (hg g (by simp))]
    rfl

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem wordCompile_legal {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) : WellFormedAdjointCircuit (wordCompile gs) := by
  induction gs with
  | nil => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  | cons g gs ih =>
    have ht : wordLegal gs := fun a ha => hg a (by simp [ha])
    change WellFormedAdjointCircuit (wordCompile (g::gs))
    rw [show g::gs=[g]++gs from rfl,wordCompile_append]
    simpa [wordCompile] using (ih ht).append (compile_legal g (hg g (by simp)))

/-- Construction for inverse in the native mixed word model. -/
def inverse {N : ℕ} : Gate N → Gate N
  | .known g => .known (NativeKnown.inverse g)
  | .forward => .backward
  | .backward => .forward

/-- Construction for adjoint Word in the native mixed word model. -/
def adjointWord {N : ℕ} (gs : List (Gate N)) : List (Gate N) := gs.reverse.map inverse

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem inverse_legal {N : ℕ} (g : Gate N) (hg : Legal g) : Legal (inverse g) := by
  cases g with
  | known g => exact NativeKnown.inverse_legal g hg
  | forward => trivial
  | backward => trivial

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem matrix_inverse {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (g : Gate N) (hg : Legal g) :
    matrix O (inverse g)=(matrix O g)ᴴ := by
  cases g with
  | known g => exact NativeKnown.matrix_inverse g hg
  | forward => rfl
  | backward => simp [matrix,inverse]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem adjointWord_legal {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) : wordLegal (adjointWord gs) := by
  intro g hmem
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hmem
  exact inverse_legal a (hg a (by simpa using ha))

/-- The finite native construction `wordMatrix_append` satisfies the displayed exact coordinate or algebraic relation. -/
theorem wordMatrix_append {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (gs hs : List (Gate N)) :
    wordMatrix O (gs++hs)=wordMatrix O hs*wordMatrix O gs := by
  induction gs with
  | nil => simp [wordMatrix]
  | cons g gs ih => simp only [List.cons_append,wordMatrix,ih,Matrix.mul_assoc]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem wordMatrix_adjoint {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (gs : List (Gate N)) (hg : wordLegal gs) :
    wordMatrix O (adjointWord gs)=(wordMatrix O gs)ᴴ := by
  induction gs with
  | nil => simp [adjointWord,wordMatrix]
  | cons g gs ih =>
    have ht : wordLegal gs := fun a ha => hg a (by simp [ha])
    simp only [adjointWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [wordMatrix_append]
    simp only [wordMatrix,Matrix.one_mul]
    change matrix O (inverse g)*wordMatrix O (adjointWord gs)=(wordMatrix O gs*matrix O g)ᴴ
    rw [matrix_inverse O g (hg g (by simp)),ih ht,Matrix.conjTranspose_mul]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem wordCompile_adjoint {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (gs : List (Gate N)) (hg : wordLegal gs) :
    evaluate O (wordCompile (adjointWord gs))=(evaluate O (wordCompile gs))ᴴ := by
  rw [wordCompile_evaluate O _ (adjointWord_legal gs hg),wordMatrix_adjoint O gs hg,wordCompile_evaluate O gs hg]

/-- The actual reverse program restores the original register under its stated premises. -/
theorem wordCompile_roundTrip {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ) (hO : O∈unitaryGroup (Reg N) ℂ)
    (gs : List (Gate N)) (hg : wordLegal gs) (ψ : QState (Reg N)) :
    ApplyGate (evaluate O (wordCompile (gs++adjointWord gs))) ψ=ψ := by
  have hu : (evaluate O (wordCompile gs))ᴴ*evaluate O (wordCompile gs)=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using
      (wordCompile_legal gs hg).evaluate_unitary hO
  rw [wordCompile_append,evaluate_append,wordCompile_adjoint O gs hg,hu,ApplyGate,Matrix.one_mulVec]

/-- Construction for query Cost in the native mixed word model. -/
def queryCost {N : ℕ} : Gate N → ℕ
  | .known _ => 0
  | _ => 1

/-- Construction for gate Cost in the native mixed word model. -/
def gateCost {N : ℕ} : Gate N → ℕ
  | .known g => NativeKnown.gateCost g
  | _ => 0

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem compile_counts {N : ℕ} (g : Gate N) :
    adjointQueryCount (compile g)=queryCost g ∧ adjointGateCount (compile g)=gateCost g := by
  cases g with
  | known g => exact ⟨(reflectionProductWord_counts _).1,
      (reflectionProductWord_counts _).2.trans (NativeKnown.compile_length g)⟩
  | forward => exact ⟨rfl,rfl⟩
  | backward => exact ⟨rfl,rfl⟩

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem wordCompile_counts {N : ℕ} (gs : List (Gate N)) :
    adjointQueryCount (wordCompile gs)=(gs.map queryCost).sum ∧
    adjointGateCount (wordCompile gs)=(gs.map gateCost).sum := by
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    rw [show g::gs=[g]++gs from rfl,wordCompile_append]
    have hc : wordCompile [g]=compile g := by simp [wordCompile]
    rw [hc,adjointQueryCount_append,adjointGateCount_append,(compile_counts g).1,(compile_counts g).2,
      ih.1,ih.2]
    simp [List.map_cons,List.sum_cons,Nat.add_comm]

/-- The finite native construction `inverse_queryCost` satisfies the displayed exact coordinate or algebraic relation. -/
theorem inverse_queryCost {N : ℕ} (g : Gate N) : queryCost (inverse g)=queryCost g := by cases g <;> rfl

/-- The finite native construction `inverse_gateCost` satisfies the displayed exact coordinate or algebraic relation. -/
theorem inverse_gateCost {N : ℕ} (g : Gate N) : gateCost (inverse g)=gateCost g := by
  cases g with
  | known g => exact NativeKnown.inverse_gateCost g
  | forward => rfl
  | backward => rfl

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem wordCompile_adjoint_counts {N : ℕ} (gs : List (Gate N)) :
    adjointQueryCount (wordCompile (adjointWord gs))=adjointQueryCount (wordCompile gs) ∧
    adjointGateCount (wordCompile (adjointWord gs))=adjointGateCount (wordCompile gs) := by
  rw [(wordCompile_counts _).1,(wordCompile_counts _).1,(wordCompile_counts _).2,(wordCompile_counts _).2]
  simp only [adjointWord,List.map_map,Function.comp_def,inverse_queryCost,inverse_gateCost,
    List.map_reverse,List.sum_reverse,and_self]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeMixed
