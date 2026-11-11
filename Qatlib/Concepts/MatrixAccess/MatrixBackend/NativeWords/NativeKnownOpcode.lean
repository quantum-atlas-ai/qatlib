/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnownControlled
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeAndLadder

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! Typed source-known opcodes and their exact fifteen/six/one-gate
refinement. The adjoint changes Circle sine signs and leaves H/X/Z/CX/CCX
unchanged, matching the source's known-operation inverse convention. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
open Qatlib Matrix
open scoped Classical

/-- Constructors for Gate in the native known opcode model. -/
inductive Gate (N : ℕ) where
  | h : Fin N → Gate N
  | x : Fin N → Gate N
  | z : Fin N → Gate N
  | cx : Fin N → Fin N → Gate N
  | ccx : Fin N → Fin N → Fin N → Gate N
  | cry : Fin N → Fin N → Circle → Gate N
  | phase : Fin N → Circle → Gate N

/-- Construction for Legal in the native known opcode model. -/
def Legal {N : ℕ} : Gate N → Prop
  | .cx c t => c≠t
  | .ccx a b t => a≠b ∧ a≠t ∧ b≠t
  | .cry c t _ => c≠t
  | _ => True

/-- Construction for legal Check in the native known opcode model. -/
def legalCheck {N : ℕ} : Gate N → Bool
  | .cx c t => c.val != t.val
  | .ccx a b t => (a.val != b.val) && (a.val != t.val) && (b.val != t.val)
  | .cry c t _ => c.val != t.val
  | _ => true

/-- The finite Boolean check accepts exactly the legal native words or opcodes. -/
theorem legalCheck_iff {N : ℕ} (g : Gate N) : legalCheck g=true ↔ Legal g := by
  cases g <;> simp [legalCheck, Legal, Fin.ext_iff, and_assoc]

/-- Construction for matrix in the native known opcode model. -/
def matrix {N : ℕ} : Gate N → Matrix (Reg N) (Reg N) ℂ
  | .h w => wireGate N w Hadamard
  | .x w => wireGate N w PauliX
  | .z w => wireGate N w PauliZ
  | .cx c t => cnotGate N c t
  | .ccx a b t => Qatlib.Concepts.GateVocabulary.GateVocab.toffoliGate a b t
  | .cry c t r => nativeControlled c t (rotation r)
  | .phase w r => wireGate N w (phaseMatrix r)

/-- Construction for inverse in the native known opcode model. -/
def inverse {N : ℕ} : Gate N → Gate N
  | .cry c t r => .cry c t r.inv
  | .phase w r => .phase w r.inv
  | g => g

/-- Construction for compile in the native known opcode model. -/
def compile {N : ℕ} : Gate N → List (ReflectionGate N)
  | .h w => [.inl (w,Hadamard)]
  | .x w => [.inl (w,PauliX)]
  | .z w => [.inl (w,PauliZ)]
  | .cx c t => [.inr (c,t)]
  | .ccx a b t => toffoliLocalSteps a b t
  | .cry c t r => multiKnownPairSteps c t (nativeCircleAngles r)
  | .phase w r => [.inl (w,phaseMatrix r)]

/-- Construction for gate Cost in the native known opcode model. -/
def gateCost {N : ℕ} : Gate N → ℕ
  | .ccx _ _ _ => 15
  | .cry _ _ _ => 6
  | _ => 1

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem inverse_legal {N : ℕ} (g : Gate N) (hg : Legal g) : Legal (inverse g) := by
  cases g <;> exact hg

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem matrix_inverse {N : ℕ} (g : Gate N) (hg : Legal g) : matrix (inverse g)=(matrix g)ᴴ := by
  have hx : PauliXᴴ=PauliX := permMatrix_conjTranspose (fun b => by cases b <;> rfl)
  cases g with
  | h w => simp [inverse, matrix, wireGate_conjTranspose, hadamard_conjTranspose]
  | x w => simp [inverse, matrix, wireGate_conjTranspose, hx]
  | z w => simp [inverse, matrix, wireGate_conjTranspose, pauliZ_conjTranspose]
  | cx c t => exact (permMatrix_conjTranspose (cnotUpdate_involutive N c t hg)).symm
  | ccx a b t => exact (permMatrix_conjTranspose
      (Qatlib.Concepts.GateVocabulary.GateVocab.toffoliUpdate_involutive a b t hg.2.1 hg.2.2)).symm
  | cry c t r => simp [inverse, matrix, nativeControlled_adjoint]
  | phase w r => simp [inverse, matrix, wireGate_conjTranspose]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem compile_legal {N : ℕ} (g : Gate N) (hg : Legal g) : reflectionLegal (compile g) := by
  cases g with
  | h w =>
    intro a ha
    have he : a=.inl (w,Hadamard) := by simpa [compile] using ha
    subst a
    exact hadamard_unitary
  | x w =>
    intro a ha
    have he : a=.inl (w,PauliX) := by simpa [compile] using ha
    subst a
    exact pauliX_unitary
  | z w =>
    intro a ha
    have he : a=.inl (w,PauliZ) := by simpa [compile] using ha
    subst a
    exact pauliZ_unitary
  | cx c t =>
    intro a ha
    have he : a=.inr (c,t) := by simpa [compile] using ha
    subst a
    exact hg
  | ccx a b t => exact toffoliLocalSteps_legal a b t hg.1 hg.2.1 hg.2.2
  | cry c t r => exact multiKnownPairSteps_legal c t hg _
  | phase w r =>
    intro a ha
    have he : a=.inl (w,phaseMatrix r) := by simpa [compile] using ha
    subst a
    exact phaseMatrix_unitary r

/-- Legality of a compiled table certifies its actual wire separation. -/
theorem legal_of_compile {N : ℕ} (g : Gate N) (hg : reflectionLegal (compile g)) : Legal g := by
  cases g with
  | h _ | x _ | z _ | phase _ _ => trivial
  | cx c t => exact hg (.inr (c,t)) (by simp [compile])
  | cry c t r => exact hg (.inr (c,t)) (by simp [compile, multiKnownPairSteps])
  | ccx a b t =>
    have hh : ccxTriplesLegal [(a,b,t)] := ccxTriplesLegal_of_compile _
      (by simpa [ccxTriplesCompile,compile] using hg)
    exact hh (a,b,t) (by simp)

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem compile_matrix {N : ℕ} (g : Gate N) (hg : Legal g) :
    reflectionProgramMatrix (compile g)=matrix g := by
  cases g with
  | h w => simp [compile, matrix, reflectionProgramMatrix, reflectionGateMatrix]
  | x w => simp [compile, matrix, reflectionProgramMatrix, reflectionGateMatrix]
  | z w => simp [compile, matrix, reflectionProgramMatrix, reflectionGateMatrix]
  | cx c t => simp [compile, matrix, reflectionProgramMatrix, reflectionGateMatrix]
  | ccx a b t => exact Qatlib.Concepts.GateVocabulary.GateVocab.toffoli_fifteen_matrix a b t hg.1 hg.2.1 hg.2.2
  | cry c t r => exact nativeCircleSteps_matrix c t hg r
  | phase w r => simp [compile, matrix, reflectionProgramMatrix, reflectionGateMatrix]

/-- The compiled native word has exactly the stated elementary-instruction length. -/
theorem compile_length {N : ℕ} (g : Gate N) : (compile g).length=gateCost g := by
  cases g <;> simp [compile, gateCost, toffoliLocalSteps_length, multiKnownPairSteps]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
