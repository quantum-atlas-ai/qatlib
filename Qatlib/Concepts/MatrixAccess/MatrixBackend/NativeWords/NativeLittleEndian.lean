/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-! Source-compatible little-endian labels. Reuse the public positional
Fin-function equivalence, not the differently ordered bitVecEquiv. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib
open scoped BigOperators

/-- Construction for source LEEquiv in the native little endian model. -/
def sourceLEEquiv (m : ℕ) : Reg m ≃ Fin (2^m) :=
  (Equiv.piCongrRight (fun _ : Fin m => boolEquivFin2)).trans finFunctionFinEquiv

/-- The finite native construction `sourceLEEquiv_val` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_val {m : ℕ} (x : Reg m) :
    (sourceLEEquiv m x).val = ∑ j : Fin m, (if x j then 1 else 0)*2^j.val := by
  change (finFunctionFinEquiv (fun j => boolEquivFin2 (x j))).val = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x j <;> rfl

/-- The finite native construction `sourceLEEquiv_decode` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_decode (m : ℕ) (i : Fin (2^m)) (j : Fin m) :
    (sourceLEEquiv m).symm i j = i.val.testBit j.val := by
  change (if (finFunctionFinEquiv.symm i j : Fin 2)=0 then false else true) = _
  simp only [Fin.ext_iff, Fin.val_zero]
  change (if i.val / 2^j.val % 2=0 then false else true) = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : i.val / 2^j.val % 2=0
  · simp [h]
  · have hmod : i.val / 2^j.val % 2=1 := by
      have := Nat.mod_lt (i.val / 2^j.val) (by decide : 0<2)
      omega
    simp [hmod]

/-- The finite native construction `sourceLEEquiv_encode_bit` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_encode_bit {m : ℕ} (x : Reg m) (j : Fin m) :
    (sourceLEEquiv m x).val.testBit j.val = x j :=
  (sourceLEEquiv_decode m (sourceLEEquiv m x) j).symm.trans
    (congrFun ((sourceLEEquiv m).symm_apply_apply x) j)

/-- The finite native construction `sourceLEEquiv_zero` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_zero (m : ℕ) : sourceLEEquiv m (fun _ => false) = 0 := by
  apply Fin.ext
  rw [sourceLEEquiv_val]
  simp

/-- The finite native construction `sourceLEEquiv_decode_zero` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_decode_zero (m : ℕ) : (sourceLEEquiv m).symm 0 = fun _ => false := by
  funext j
  rw [sourceLEEquiv_decode]
  simp

/-- The finite native construction `sourceLEEquiv_eq_zero_iff` satisfies the displayed exact coordinate or algebraic relation. -/
theorem sourceLEEquiv_eq_zero_iff {m : ℕ} (x : Reg m) :
    sourceLEEquiv m x=0 ↔ ∀ j,x j=false := by
  constructor
  · intro h j
    have hh := congrFun (congrArg (sourceLEEquiv m).symm h) j
    simpa only [Equiv.symm_apply_apply, sourceLEEquiv_decode_zero] using hh
  · intro h
    have hx : x=(fun _ => false) := funext h
    rw [hx, sourceLEEquiv_zero]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
