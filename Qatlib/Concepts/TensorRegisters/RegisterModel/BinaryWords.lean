/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords
set_option autoImplicit false
noncomputable section

def bitValue (b : Bool) : ℕ := if b then 1 else 0

theorem bitEquiv_value (b : Bool) : (finTwoEquiv.symm b).val = bitValue b := by
  cases b <;> rfl

def blockEquiv : (u : ℕ) → (Fin u → Bool) ≃ Fin (2^u)
  | 0 => { toFun := fun _ => 0
           invFun := fun _ i => Fin.elim0 i
           left_inv := fun _ => Subsingleton.elim _ _
           right_inv := fun i => Fin.ext (by have := i.isLt; norm_num at *) }
  | u+1 => (Fin.consEquiv (fun _ : Fin (u+1) => Bool)).symm |>.trans
      ((Equiv.prodComm Bool (Fin u → Bool)).trans
        ((Equiv.prodCongr (blockEquiv u) finTwoEquiv.symm).trans
          (finProdFinEquiv.trans (finCongr (by omega : 2^u * 2 = 2^(u+1))))))

theorem blockEquiv_value (u : ℕ) (x : Fin u → Bool) :
    (blockEquiv u x).val = ∑ j : Fin u, bitValue (x j) * 2^j.val := by
  induction u with
  | zero => simp [blockEquiv]
  | succ u ih =>
    change (finTwoEquiv.symm (x 0)).val + 2 * (blockEquiv u (Fin.tail x)).val = _
    rw [bitEquiv_value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    have ht (j : Fin u) : bitValue (x j.succ) * (2^j.val * 2) =
        2 * (bitValue (Fin.tail x j) * 2^j.val) := by
      change bitValue (x j.succ) * (2^j.val * 2) = 2 * (bitValue (x j.succ) * 2^j.val)
      ring
    simp_rw [ht]
    rw [← Finset.mul_sum]
end
end Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords
