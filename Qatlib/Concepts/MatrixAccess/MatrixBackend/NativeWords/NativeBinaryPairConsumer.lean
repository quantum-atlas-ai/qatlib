/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeBitPair
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeLabelPadding
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
/-! The constructed binary pair operator consumes the source-compatible
padding frame and realizes the supplied logical table gate. The pivot
condition is its actual integer set-bit condition, not a matrix premise. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for source Binary Pair in the native binary pair consumer model. -/
def sourceBinaryPair (m n : ℕ) (h : n+1≤2^m) (i : Fin n) (pivot : Fin m) (r : Circle) :
    Matrix (Reg m) (Reg m) ℂ :=
  nativePairGate (binaryPairControls pivot) pivot
    (binaryPairTargets pivot (sourceLabelBits m n h (some i))) r

/-- The finite native construction `weightTwoLevel_ket_none` satisfies the displayed exact coordinate or algebraic relation. -/
private theorem weightTwoLevel_ket_none {n : ℕ} (i : Fin n) (r : Circle) :
    weightTwoLevel i (r.c : ℂ) (r.s : ℂ) *ᵥ Qatlib.Foundations.PureStateMath.Ket none =
      (r.c : ℂ) • Qatlib.Foundations.PureStateMath.Ket none + (r.s : ℂ) • Qatlib.Foundations.PureStateMath.Ket (some i) := by
  funext a
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  cases a with
  | none => simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket]
  | some j => by_cases hj : j=i <;> simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket, hj]

/-- The finite native construction `weightTwoLevel_ket_some` satisfies the displayed exact coordinate or algebraic relation. -/
private theorem weightTwoLevel_ket_some {n : ℕ} (i : Fin n) (r : Circle) :
    weightTwoLevel i (r.c : ℂ) (r.s : ℂ) *ᵥ Qatlib.Foundations.PureStateMath.Ket (some i) =
      -(r.s : ℂ) • Qatlib.Foundations.PureStateMath.Ket none + (r.c : ℂ) • Qatlib.Foundations.PureStateMath.Ket (some i) := by
  funext a
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  cases a with
  | none => simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket]
  | some j => by_cases hj : j=i <;> simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket, hj]

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
private theorem weightTwoLevel_ket_other {n : ℕ} (i j : Fin n) (r : Circle) (hj : j≠i) :
    weightTwoLevel i (r.c : ℂ) (r.s : ℂ) *ᵥ Qatlib.Foundations.PureStateMath.Ket (some j) = Qatlib.Foundations.PureStateMath.Ket (some j) := by
  funext a
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  cases a with
  | none => simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket, hj]
  | some k => simp [weightTwoLevel, Qatlib.Foundations.PureStateMath.Ket, Ne.symm hj, eq_comm]

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem sourceBinaryPair_frame (m n : ℕ) (h : n+1≤2^m) (i : Fin n) (pivot : Fin m) (r : Circle)
    (hp : (i.val+1).testBit pivot.val=true) :
    sourceBinaryPair m n h i pivot r * sourceLabelFrame m n h =
      sourceLabelFrame m n h * weightTwoLevel i (r.c : ℂ) (r.s : ℂ) := by
  have hm : sourceLabelBits m n h (some i) pivot=true := by
    simpa only [sourceLabelBits_some] using hp
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro a
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sourceLabelFrame_ket]
  cases a with
  | none =>
    rw [weightTwoLevel_ket_none, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      sourceLabelFrame_ket, sourceLabelFrame_ket, sourceLabelBits_none]
    exact binaryPairGate_zero pivot _ hm r
  | some j =>
    by_cases hji : j=i
    · subst j
      rw [weightTwoLevel_ket_some, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        sourceLabelFrame_ket, sourceLabelFrame_ket, sourceLabelBits_none]
      exact binaryPairGate_mask pivot _ hm r
    · rw [weightTwoLevel_ket_other i j r hji, sourceLabelFrame_ket]
      have hx0 : sourceLabelBits m n h (some j)≠(fun _ => false) := by
        intro he
        have hh : sourceLabelBits m n h (some j)=sourceLabelBits m n h none :=
          he.trans (sourceLabelBits_none m n h).symm
        cases sourceLabelBits_injective m n h hh
      have hxm : sourceLabelBits m n h (some j)≠sourceLabelBits m n h (some i) := by
        intro he
        exact hji (Option.some.inj (sourceLabelBits_injective m n h he))
      exact binaryPairGate_other pivot _ _ hm r hx0 hxm

/-- Padded binary columns of V are fixed; this does not assert that the
conjugated Householder PREP has +I padding. Its origin reflection negates it. -/
theorem sourceBinaryPair_padding (m n : ℕ) (h : n+1≤2^m) (i : Fin n) (pivot : Fin m) (r : Circle)
    (hp : (i.val+1).testBit pivot.val=true) (x : Reg m)
    (hx : n+1≤(sourceLEEquiv m x).val) :
    ApplyGate (sourceBinaryPair m n h i pivot r) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket x := by
  have hm : sourceLabelBits m n h (some i) pivot=true := by
    simpa only [sourceLabelBits_some] using hp
  have hneq (a : Option (Fin n)) : x≠sourceLabelBits m n h a := by
    intro he
    have hh := congrArg (fun y => (sourceLEEquiv m y).val) he
    simp only [sourceLabelBits_value] at hh
    have ha := (sourceOptionIndex n a).isLt
    change (sourceLEEquiv m x).val=(sourceOptionIndex n a).val at hh
    omega
  have hx0 : x≠(fun _ => false) := by simpa only [sourceLabelBits_none] using hneq none
  exact binaryPairGate_other pivot _ x hm r hx0 (hneq (some i))

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
