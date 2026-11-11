/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeBinaryPairConsumer
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! Identify the already derived binary pair columns with the pinned generic
two-coordinate block, then reuse its unitarity. No different circuit
producer is used to certify the source word. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- The finite native construction `binaryPairGate_eq_twoLevel` satisfies the displayed exact coordinate or algebraic relation. -/
theorem binaryPairGate_eq_twoLevel {m : ℕ} (pivot : Fin m) (mask : Reg m)
    (hp : mask pivot=true) (r : Circle) :
    nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r =
      twoLevelMatrix (.pair (fun _ => false) mask (rotation r)) := by
  have hzero : (fun _ => false)≠mask := by
    intro he
    have hh := congrFun he pivot
    rw [hp] at hh
    cases hh
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro x
  by_cases hx0 : x=(fun _ => false)
  · subst x
    change ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) = _
    rw [binaryPairGate_zero pivot mask hp r]
    funext row
    change _ = (twoLevelMatrix (.pair (fun _ => false) mask (rotation r)) *ᵥ Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) row
    rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
    by_cases hr0 : row=(fun _ => false) <;> by_cases hrm : row=mask <;>
      simp_all [twoLevelMatrix, rotation, Qatlib.Foundations.PureStateMath.Ket]
  · by_cases hxm : x=mask
    · subst x
      change ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket mask) = _
      rw [binaryPairGate_mask pivot mask hp r]
      funext row
      change _ = (twoLevelMatrix (.pair (fun _ => false) mask (rotation r)) *ᵥ Qatlib.Foundations.PureStateMath.Ket mask) row
      rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
      by_cases hr0 : row=(fun _ => false) <;> by_cases hrm : row=mask <;>
        simp_all [twoLevelMatrix, rotation, Qatlib.Foundations.PureStateMath.Ket]
    · change ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x) = _
      rw [binaryPairGate_other pivot mask x hp r hx0 hxm]
      have hx0r := Ne.symm hx0
      have hxmr := Ne.symm hxm
      funext row
      change _ = (twoLevelMatrix (.pair (fun _ => false) mask (rotation r)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) row
      rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
      by_cases hr0 : row=(fun _ => false) <;> by_cases hrm : row=mask <;>
        simp_all [twoLevelMatrix, Qatlib.Foundations.PureStateMath.Ket]

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem binaryPairGate_unitary {m : ℕ} (pivot : Fin m) (mask : Reg m)
    (hp : mask pivot=true) (r : Circle) :
    nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r ∈
      unitaryGroup (Reg m) ℂ := by
  rw [binaryPairGate_eq_twoLevel pivot mask hp r]
  apply twoLevel_pair_unitary _ _ _ _ (rotation_unitary r)
  intro he
  have hh := congrFun he pivot
  rw [hp] at hh
  cases hh

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem sourceBinaryPair_unitary (m n : ℕ) (h : n+1≤2^m) (i : Fin n) (pivot : Fin m) (r : Circle)
    (hp : (i.val+1).testBit pivot.val=true) :
    sourceBinaryPair m n h i pivot r ∈ unitaryGroup (Reg m) ℂ :=
  binaryPairGate_unitary pivot _ (by simpa only [sourceLabelBits_some] using hp) r

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
