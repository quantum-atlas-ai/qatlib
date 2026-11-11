/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeLittleEndian
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! Source label zero is `none`, and `some i` has integer code i+1.
The actual little-endian padding frame supports arbitrary active sizes;
it does not impose a power-of-two equality or choose padding gate signs. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped BigOperators

/-- Construction for source Option Index in the native label padding model. -/
def sourceOptionIndex (n : ℕ) : Option (Fin n) ≃ Fin (n+1) :=
  (finSuccEquiv' (0 : Fin (n+1))).symm

/-- The finite native construction `sourceOptionIndex_none` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem sourceOptionIndex_none (n : ℕ) : sourceOptionIndex n none=0 := rfl

/-- The finite native construction `sourceOptionIndex_some` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem sourceOptionIndex_some {n : ℕ} (i : Fin n) :
    sourceOptionIndex n (some i)=i.succ := by simp [sourceOptionIndex]

/-- Construction for source Label Bits in the native label padding model. -/
def sourceLabelBits (m n : ℕ) (h : n+1 ≤ 2^m) (a : Option (Fin n)) : Reg m :=
  (sourceLEEquiv m).symm (Fin.castLE h (sourceOptionIndex n a))

/-- The finite native construction `sourceLabelBits_value` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem sourceLabelBits_value (m n : ℕ) (h : n+1 ≤ 2^m) (a : Option (Fin n)) :
    sourceLEEquiv m (sourceLabelBits m n h a) = Fin.castLE h (sourceOptionIndex n a) :=
  (sourceLEEquiv m).apply_symm_apply _

/-- The finite native construction `sourceLabelBits_injective` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLabelBits_injective (m n : ℕ) (h : n+1 ≤ 2^m) :
    Function.Injective (sourceLabelBits m n h) := by
  intro a b he
  have hh := congrArg (sourceLEEquiv m) he
  simp only [sourceLabelBits_value] at hh
  apply (sourceOptionIndex n).injective
  apply Fin.ext
  simpa using congrArg (fun z : Fin (2^m) => z.val) hh

/-- The finite native construction `sourceLabelBits_none` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem sourceLabelBits_none (m n : ℕ) (h : n+1 ≤ 2^m) :
    sourceLabelBits m n h none = fun _ => false := by
  change (sourceLEEquiv m).symm (0 : Fin (2^m)) = _
  exact sourceLEEquiv_decode_zero m

/-- The finite native construction `sourceLabelBits_some` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLabelBits_some (m n : ℕ) (h : n+1 ≤ 2^m) (i : Fin n) (j : Fin m) :
    sourceLabelBits m n h (some i) j = (i.val+1).testBit j.val := by
  rw [sourceLabelBits, sourceLEEquiv_decode]
  simp

/-- Construction for source Decode Label in the native label padding model. -/
def sourceDecodeLabel (m n : ℕ) (x : Reg m) : Option (Option (Fin n)) :=
  if h : (sourceLEEquiv m x).val < n+1 then
    some ((sourceOptionIndex n).symm ⟨(sourceLEEquiv m x).val,h⟩)
  else none

/-- The finite native construction `sourceDecodeLabel_encode` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem sourceDecodeLabel_encode (m n : ℕ) (h : n+1 ≤ 2^m) (a : Option (Fin n)) :
    sourceDecodeLabel m n (sourceLabelBits m n h a)=some a := by
  simp [sourceDecodeLabel, (sourceOptionIndex n a).isLt]

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem sourceDecodeLabel_padding_iff (m n : ℕ) (x : Reg m) :
    sourceDecodeLabel m n x=none ↔ n+1 ≤ (sourceLEEquiv m x).val := by
  unfold sourceDecodeLabel
  split <;> simp_all
  omega

noncomputable section
open scoped Classical

/-- Construction for source Label Frame in the native label padding model. -/
def sourceLabelFrame (m n : ℕ) (h : n+1 ≤ 2^m) : Matrix (Reg m) (Option (Fin n)) ℂ :=
  fun x a => Qatlib.Foundations.PureStateMath.Ket (sourceLabelBits m n h a) x

/-- The concrete rectangular frame has identity Gram matrix. -/
theorem sourceLabelFrame_isometry (m n : ℕ) (h : n+1 ≤ 2^m) :
    IsIsometry (sourceLabelFrame m n h) := by
  unfold IsIsometry
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sourceLabelFrame, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single (sourceLabelBits m n h a)]
  · by_cases hab : a=b
    · subst b
      simp
    · have he : sourceLabelBits m n h a≠sourceLabelBits m n h b :=
        fun he => hab (sourceLabelBits_injective m n h he)
      simp [hab, he]
  · intro x _ hxa
    simp [hxa]
  · intro ha
    exact False.elim (ha (Finset.mem_univ _))

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem sourceLabelFrame_ket (m n : ℕ) (h : n+1 ≤ 2^m) (a : Option (Fin n)) :
    sourceLabelFrame m n h *ᵥ Qatlib.Foundations.PureStateMath.Ket a = Qatlib.Foundations.PureStateMath.Ket (sourceLabelBits m n h a) := by
  funext x
  change (∑ b,sourceLabelFrame m n h x b * Qatlib.Foundations.PureStateMath.Ket a b) = _
  rw [Finset.sum_eq_single a]
  · simp [Qatlib.Foundations.PureStateMath.Ket, sourceLabelFrame]
  · intro b _ hba
    simp [Qatlib.Foundations.PureStateMath.Ket, hba]
  · intro ha
    exact False.elim (ha (Finset.mem_univ _))

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem sourceLabelFrame_padding_row (m n : ℕ) (h : n+1 ≤ 2^m) (x : Reg m)
    (hp : n+1 ≤ (sourceLEEquiv m x).val) (a : Option (Fin n)) :
    sourceLabelFrame m n h x a=0 := by
  have he : x≠sourceLabelBits m n h a := by
    intro he
    have hv := congrArg (fun y => (sourceLEEquiv m y).val) he
    simp only [sourceLabelBits_value] at hv
    have hi := (sourceOptionIndex n a).isLt
    change (sourceLEEquiv m x).val = (sourceOptionIndex n a).val at hv
    omega
  simp [sourceLabelFrame, Qatlib.Foundations.PureStateMath.Ket, he]

end
end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
