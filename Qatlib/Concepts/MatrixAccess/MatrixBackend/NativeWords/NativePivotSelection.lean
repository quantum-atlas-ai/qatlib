/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeLabelPadding
import Mathlib.Data.List.FinRange

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

/-! Executable bounded lowest-set-bit scan. The returned data uses findIdx,
not a classical choice; nonzero masks prove the scan succeeds in width m. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem exists_setBit {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) : ∃ j,x j=true := by
  classical
  by_contra hh
  apply hx
  funext j
  exact Bool.eq_false_of_not_eq_true (fun hj => hh ⟨j,hj⟩)

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem setBit_findIdx_lt {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) :
    (List.finRange m).findIdx x < m := by
  obtain ⟨j,hj⟩ := exists_setBit x hx
  have hh := List.findIdx_lt_length_of_exists (xs := List.finRange m) (p := x) ⟨j,by simp,hj⟩
  simpa using hh

/-- Construction for first Set Bit in the native pivot selection model. -/
def firstSetBit {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) : Fin m :=
  ⟨(List.finRange m).findIdx x,setBit_findIdx_lt x hx⟩

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem firstSetBit_true {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) : x (firstSetBit x hx)=true := by
  have hlt : (List.finRange m).findIdx x < (List.finRange m).length := by
    simpa using setBit_findIdx_lt x hx
  have hh := List.findIdx_getElem (xs := List.finRange m) (p := x) (w := hlt)
  simpa [firstSetBit] using hh

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem firstSetBit_minimal {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) (j : Fin m)
    (hj : j.val < (firstSetBit x hx).val) : x j=false := by
  have hh := List.not_of_lt_findIdx (p := x) (xs := List.finRange m) (i := j.val) hj
  simpa using hh

/-- Construction for pivot Scan Tests in the native pivot selection model. -/
def pivotScanTests {m : ℕ} : List (Fin m) → Reg m → ℕ
  | [],_ => 0
  | j::js,x => if x j then 1 else 1+pivotScanTests js x

/-- The compiled native word has exactly the stated elementary-instruction length. -/
theorem pivotScanTests_le_length {m : ℕ} (js : List (Fin m)) (x : Reg m) :
    pivotScanTests js x ≤ js.length := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases hj : x j with
    | false =>
      simp [pivotScanTests, hj]
      omega
    | true => simp [pivotScanTests, hj]

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem pivotScanTests_eq_findIdx_succ {m : ℕ} (js : List (Fin m)) (x : Reg m)
    (hh : ∃ j∈js,x j=true) : pivotScanTests js x=js.findIdx x+1 := by
  induction js with
  | nil => simp at hh
  | cons j js ih =>
    by_cases hj : x j=true
    · simp [pivotScanTests, List.findIdx_cons, hj]
    · have ht : ∃ k∈js,x k=true := by
        obtain ⟨k,hk,hx⟩ := hh
        rcases List.mem_cons.mp hk with rfl|hk
        · exact False.elim (hj hx)
        · exact ⟨k,hk,hx⟩
      simp [pivotScanTests, List.findIdx_cons, hj, ih ht]
      omega

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem firstSetBit_tests {m : ℕ} (x : Reg m) (hx : x≠fun _ => false) :
    pivotScanTests (List.finRange m) x=(firstSetBit x hx).val+1 ∧
      pivotScanTests (List.finRange m) x≤m := by
  obtain ⟨j,hj⟩ := exists_setBit x hx
  exact ⟨pivotScanTests_eq_findIdx_succ _ x ⟨j,by simp,hj⟩,
    by simpa using pivotScanTests_le_length (List.finRange m) x⟩

/-- The finite native construction `sourceLabelBits_nonzero` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLabelBits_nonzero (m n : ℕ) (h : n+1≤2^m) (i : Fin n) :
    sourceLabelBits m n h (some i)≠(fun _ => false) := by
  intro he
  have hh : sourceLabelBits m n h (some i)=sourceLabelBits m n h none :=
    he.trans (sourceLabelBits_none m n h).symm
  cases sourceLabelBits_injective m n h hh

/-- Construction for source Pivots in the native pivot selection model. -/
def sourcePivots (m n : ℕ) (h : n+1≤2^m) (i : Fin n) : Fin m :=
  firstSetBit (sourceLabelBits m n h (some i)) (sourceLabelBits_nonzero m n h i)

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem sourcePivots_bit (m n : ℕ) (h : n+1≤2^m) (i : Fin n) :
    (i.val+1).testBit (sourcePivots m n h i).val=true := by
  have hh := firstSetBit_true (sourceLabelBits m n h (some i)) (sourceLabelBits_nonzero m n h i)
  simpa only [sourcePivots,sourceLabelBits_some] using hh

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem sourcePivots_div_mod (m n : ℕ) (h : n+1≤2^m) (i : Fin n) :
    (i.val+1) / 2^(sourcePivots m n h i).val % 2=1 := by
  have hh := sourcePivots_bit m n h i
  simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] using hh

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem sourcePivots_minimal (m n : ℕ) (h : n+1≤2^m) (i : Fin n) (j : Fin m)
    (hj : j.val < (sourcePivots m n h i).val) : (i.val+1).testBit j.val=false := by
  have hh := firstSetBit_minimal (sourceLabelBits m n h (some i)) (sourceLabelBits_nonzero m n h i) j hj
  simpa only [sourcePivots,sourceLabelBits_some] using hh

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
