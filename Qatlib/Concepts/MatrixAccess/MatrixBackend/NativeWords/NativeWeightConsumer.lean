/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightProgram

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! The refined physical PREP is consumed on the explicit active frame,
including arbitrary original data frames. Its rational output column is
derived from the word, not supplied as a PREP correctness assumption. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical Kronecker

/-- The actual native program gives the displayed projected unitary encoding. -/
theorem weightRefinedPrepWord_encoding (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    ProjectedUnitaryEncoding (tableHouseholder rs)
      (reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs))
      (weightFrame m w * sourceLabelFrame m n h) (weightFrame m w * sourceLabelFrame m n h) := by
  have hs := Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (weightFrame_isometry m w) (sourceLabelFrame_isometry m n h)
  refine ⟨reflectionProgramMatrix_unitary _ (weightRefinedPrepWord_legal m w n h pivots rs hw),hs,hs,?_⟩
  unfold compress
  rw [Matrix.mul_assoc, weightRefinedPrepWord_active_frame m w n h pivots rs hw hp,
    ← Matrix.mul_assoc, hs, Matrix.one_mul]

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem weightRefinedPrepWord_origin_input (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) (x : Reg m) :
    reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs)
      (weightInput m w x) (weightInput m w (fun _ => false)) =
      sourceBinaryHouseholder m n h pivots rs x (fun _ => false) := by
  have hh := congrArg (fun M => M *ᵥ Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))
    (weightRefinedPrepWord_frame m w n h pivots rs hw hp)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, weightFrame_ket] at hh
  have hr := congrFun hh (weightInput m w x)
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply, weightFrame_apply_at_input, Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply] at hr
  exact hr

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem weightRefinedPrepWord_origin_valid (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) (a : Option (Fin n)) :
    reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs)
      (weightInput m w (sourceLabelBits m n h a)) (weightInput m w (fun _ => false)) =
      (tablePreparedColumn rs a : ℂ) := by
  rw [weightRefinedPrepWord_origin_input m w n h pivots rs hw hp,
    sourceBinaryHouseholder_origin_valid m n h pivots rs hp]

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem weightRefinedPrepWord_origin_padding_zero (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) (x : Reg m)
    (hx : n+1≤(sourceLEEquiv m x).val) :
    reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs)
      (weightInput m w x) (weightInput m w (fun _ => false)) = 0 := by
  rw [weightRefinedPrepWord_origin_input m w n h pivots rs hw hp,
    sourceBinaryHouseholder_origin_padding_zero m n h pivots rs hp x hx]

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightRefinedPrepWord_active_tensor_frame {H I : Type*} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) (F : Matrix H I ℂ) :
    (reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs) ⊗ₖ (1 : Matrix H H ℂ)) *
      ((weightFrame m w * sourceLabelFrame m n h) ⊗ₖ F) =
      ((weightFrame m w * sourceLabelFrame m n h) ⊗ₖ F) *
        (tableHouseholder rs ⊗ₖ (1 : Matrix I I ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    weightRefinedPrepWord_active_frame m w n h pivots rs hw hp]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
