/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnownOpcode

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! Complete typed known-word refinement and native inverse compilation.
All matrix statements are global, including initially dirty work/seed and
arbitrary coherent garbage. No clean-subspace premise is used. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
open Qatlib Matrix
open scoped Classical Kronecker

/-- Construction for word Compile in the native known word model. -/
def wordCompile {N : ℕ} (gs : List (Gate N)) : List (ReflectionGate N) := gs.flatMap compile
/-- Construction for word Legal in the native known word model. -/
def wordLegal {N : ℕ} (gs : List (Gate N)) : Prop := ∀ g∈gs,Legal g

/-- Construction for word Legal Check in the native known word model. -/
def wordLegalCheck {N : ℕ} (gs : List (Gate N)) : Bool := gs.all legalCheck

/-- The finite Boolean check accepts exactly the legal native words or opcodes. -/
theorem wordLegalCheck_iff {N : ℕ} (gs : List (Gate N)) : wordLegalCheck gs=true ↔ wordLegal gs := by
  simp only [wordLegalCheck, List.all_eq_true, legalCheck_iff, wordLegal]

/-- Construction for word Matrix in the native known word model. -/
def wordMatrix {N : ℕ} : List (Gate N) → Matrix (Reg N) (Reg N) ℂ
  | [] => 1
  | g::gs => wordMatrix gs * matrix g

/-- Construction for adjoint Word in the native known word model. -/
def adjointWord {N : ℕ} (gs : List (Gate N)) : List (Gate N) := gs.reverse.map inverse

/-- The finite native construction `wordCompile_append` satisfies the displayed exact coordinate or algebraic relation. -/
theorem wordCompile_append {N : ℕ} (gs hs : List (Gate N)) :
    wordCompile (gs++hs)=wordCompile gs++wordCompile hs := List.flatMap_append

/-- The finite native construction `wordMatrix_append` satisfies the displayed exact coordinate or algebraic relation. -/
theorem wordMatrix_append {N : ℕ} (gs hs : List (Gate N)) :
    wordMatrix (gs++hs)=wordMatrix hs*wordMatrix gs := by
  induction gs with
  | nil => simp [wordMatrix]
  | cons g gs ih => simp only [List.cons_append, wordMatrix, ih, Matrix.mul_assoc]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem wordCompile_legal {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) :
    reflectionLegal (wordCompile gs) := by
  intro a ha
  obtain ⟨g,hgmem,ha⟩ := List.mem_flatMap.mp ha
  exact compile_legal g (hg g hgmem) a ha

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem wordLegal_of_compile {N : ℕ} (gs : List (Gate N)) (hg : reflectionLegal (wordCompile gs)) :
    wordLegal gs := by
  intro g hmem
  apply legal_of_compile g
  intro a ha
  exact hg a (List.mem_flatMap.mpr ⟨g,hmem,ha⟩)

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem wordCompile_matrix {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) :
    reflectionProgramMatrix (wordCompile gs)=wordMatrix gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ht : wordLegal gs := fun a ha => hg a (by simp [ha])
    simp only [wordCompile, List.flatMap_cons, reflectionProgramMatrix_append]
    rw [compile_matrix g (hg g (by simp)), ← wordCompile, ih ht]
    rfl

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem adjointWord_legal {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) : wordLegal (adjointWord gs) := by
  intro a ha
  obtain ⟨g,hgmem,rfl⟩ := List.mem_map.mp ha
  exact inverse_legal g (hg g (List.mem_reverse.mp hgmem))

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem wordMatrix_adjoint {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) :
    wordMatrix (adjointWord gs)=(wordMatrix gs)ᴴ := by
  induction gs with
  | nil => simp [adjointWord, wordMatrix]
  | cons g gs ih =>
    have ht : wordLegal gs := fun a ha => hg a (by simp [ha])
    simp only [adjointWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [wordMatrix_append]
    simp only [wordMatrix, Matrix.one_mul]
    change matrix (inverse g)*wordMatrix (adjointWord gs)=(wordMatrix gs*matrix g)ᴴ
    rw [matrix_inverse g (hg g (by simp)), ih ht, Matrix.conjTranspose_mul]

/-- Compile the source's native inverse, not the syntactic adjoint of an
independently expanded table: these have equal operators on the full space. -/
theorem wordCompile_adjoint {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) :
    reflectionProgramMatrix (wordCompile (adjointWord gs)) =
      (reflectionProgramMatrix (wordCompile gs))ᴴ := by
  rw [wordCompile_matrix _ (adjointWord_legal gs hg), wordMatrix_adjoint gs hg, wordCompile_matrix gs hg]

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem wordMatrix_unitary {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) :
    wordMatrix gs ∈ unitaryGroup (Reg N) ℂ := by
  have hh := reflectionProgramMatrix_unitary _ (wordCompile_legal gs hg)
  rwa [wordCompile_matrix gs hg] at hh

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem wordCompile_adjoint_tensor {H : Type*} [DecidableEq H] {N : ℕ}
    (gs : List (Gate N)) (hg : wordLegal gs) :
    reflectionProgramMatrix (wordCompile (adjointWord gs)) ⊗ₖ (1 : Matrix H H ℂ) =
      (reflectionProgramMatrix (wordCompile gs) ⊗ₖ (1 : Matrix H H ℂ))ᴴ := by
  rw [wordCompile_adjoint gs hg, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- The actual native inverse restores every coherent register input,
including query-generated garbage; no clean-register condition occurs. -/
theorem wordCompile_roundTrip {N : ℕ} (gs : List (Gate N)) (hg : wordLegal gs) (ψ : QState (Reg N)) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (wordCompile (gs++adjointWord gs))) ψ=ψ := by
  have hu : (reflectionProgramMatrix (wordCompile gs))ᴴ * reflectionProgramMatrix (wordCompile gs)=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using
      reflectionProgramMatrix_unitary _ (wordCompile_legal gs hg)
  rw [run_reflectionCompile, wordCompile_append, reflectionProgramMatrix_append,
    wordCompile_adjoint gs hg, ApplyGate, hu, Matrix.one_mulVec]

/-- The compiled native word has exactly the stated elementary-instruction length. -/
theorem wordCompile_length {N : ℕ} (gs : List (Gate N)) :
    (wordCompile gs).length=(gs.map gateCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [wordCompile, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    rw [compile_length g, ← wordCompile, ih]

/-- The finite native construction `inverse_gateCost` satisfies the displayed exact coordinate or algebraic relation. -/
theorem inverse_gateCost {N : ℕ} (g : Gate N) : gateCost (inverse g)=gateCost g := by
  cases g <;> rfl

/-- The compiled native word has exactly the stated elementary-instruction length. -/
theorem wordCompile_adjoint_length {N : ℕ} (gs : List (Gate N)) :
    (wordCompile (adjointWord gs)).length=(wordCompile gs).length := by
  rw [wordCompile_length, wordCompile_length]
  simp only [adjointWord, List.map_map, Function.comp_def, inverse_gateCost]
  rw [List.map_reverse, List.sum_reverse]

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem wordCompile_counts {N : ℕ} (gs : List (Gate N)) :
    QueryCount (reflectionCompile (wordCompile gs))=0 ∧
    GateCount (reflectionCompile (wordCompile gs))=(gs.map gateCost).sum :=
  ⟨queryCount_reflectionCompile _,(gateCount_reflectionCompile _).trans (wordCompile_length gs)⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
