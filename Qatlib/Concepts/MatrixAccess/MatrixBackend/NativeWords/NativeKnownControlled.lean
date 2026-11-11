/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.SqrtApprox.ControlledWireNorm
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePredicateCircle

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.SqrtApprox
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Arbitrary-width reference semantics for the source's controlled known
one-qubit gate. The six-gate refinement is proved on every register ket,
without work/pool/seed cleanliness assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib Matrix
open scoped Classical

/-- Construction for native Controlled in the native known controlled model. -/
def nativeControlled {N : ℕ} (c t : Fin N) (B : Matrix Bool Bool ℂ) : Matrix (Reg N) (Reg N) ℂ :=
  relabelGate (elementaryWireSplit t).symm
    (BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then B else 1))

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem nativeControlled_adjoint {N : ℕ} (c t : Fin N) (B : Matrix Bool Bool ℂ) :
    (nativeControlled c t B)ᴴ=nativeControlled c t Bᴴ := by
  unfold nativeControlled
  have he : (BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then B else 1))ᴴ =
      BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then Bᴴ else 1) := by
    ext ⟨x,a⟩ ⟨y,b⟩
    by_cases h : x=y
    · subst y
      cases hx : x.1 c <;>
        simp only [BlockDiag, Matrix.of_apply, Matrix.conjTranspose_apply, hx, ↓reduceIte]
      · change ((1 : Matrix Bool Bool ℂ)ᴴ) a b=(1 : Matrix Bool Bool ℂ) a b
        rw [Matrix.conjTranspose_one]
    · simp [BlockDiag, Matrix.conjTranspose_apply, h, Ne.symm h]
  simpa only [relabelGate, Matrix.conjTranspose_reindex] using
    congrArg (relabelGate (elementaryWireSplit t).symm) he

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativeControlled_ket {N : ℕ} (c t : Fin N) (hct : c≠t)
    (B : Matrix Bool Bool ℂ) (x : Reg N) :
    ApplyGate (nativeControlled c t B) (Qatlib.Foundations.PureStateMath.Ket x) =
      if x c then B false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false)+
        B true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true) else Qatlib.Foundations.PureStateMath.Ket x := by
  funext y
  rw [show ApplyGate (nativeControlled c t B) (Qatlib.Foundations.PureStateMath.Ket x) y=nativeControlled c t B y x from Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply _ x y]
  simp only [nativeControlled, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  change (if (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 then
      (if (Function.update x t false) c then B else 1) (y t) (x t) else 0) = _
  rw [Function.update_of_ne hct]
  have he (b : Bool) : y=Function.update x t b ↔
      (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 ∧ y t=b := by
    constructor
    · intro h
      constructor
      · apply Subtype.ext
        change Function.update y t false=Function.update x t false
        rw [h, Function.update_idem]
      · rw [h, Function.update_self]
    · rintro ⟨h,hb⟩
      have hh := congrArg (fun z : ElementaryWireLabel t => Function.update z.1 t b) h
      simpa [elementaryWireSplit, Function.update_idem, ← hb] using hh
  have hyx : y=x ↔ (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 ∧ y t=x t := by
    simpa using he (x t)
  cases hc : x c <;> cases hx : x t <;> cases ht : y t <;>
    by_cases hs : (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 <;>
    simp only [hx, ht, hs, Bool.false_eq_true, ↓reduceIte, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket, he false, he true, hyx, Matrix.one_apply,
      and_true, and_false, Bool.true_eq_false, mul_zero, mul_one, add_zero, zero_add]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem nativeCircleSteps_matrix {N : ℕ} (c t : Fin N) (hct : c≠t) (r : Circle) :
    reflectionProgramMatrix (multiKnownPairSteps c t (nativeCircleAngles r)) =
      nativeControlled c t (rotation r) := by
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro x
  change ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x)=ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x)
  rw [nativeControlled_ket c t hct]
  have hh := multiKnownPairSteps_action c t hct (nativeCircleAngles r) x (Qatlib.Foundations.PureStateMath.Ket (x t))
  simp only [multiWireState_ket, nativeCircleAngles_correct, run_reflectionCompile] at hh
  rw [hh]
  cases hc : x c
  · simp [applyGate_one]
  · simp only [ite_true, multiWireState, ApplyGate, Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
