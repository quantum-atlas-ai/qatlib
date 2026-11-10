/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QGradient20.CopyBudget

inductive PreparationTree (k : ℕ) where
  | input : PreparationTree k
  | filter : (Fin k → PreparationTree k) → PreparationTree k

def inputCalls {k : ℕ} : PreparationTree k → ℕ
  | .input => 1
  | .filter children => ∑ i, inputCalls (children i)

def filterCalls {k : ℕ} : PreparationTree k → ℕ
  | .input => 0
  | .filter children => 1 + ∑ i, filterCalls (children i)

def parallelRegisters {k : ℕ} : PreparationTree k → ℕ
  | .input => 1
  | .filter children => ∑ i, parallelRegisters (children i)

def iteratedPreparation (k : ℕ) : ℕ → PreparationTree k
  | 0 => .input
  | n+1 => .filter (fun _ => iteratedPreparation k n)

theorem iterated_input_calls (k n : ℕ) : inputCalls (iteratedPreparation k n)=k^n := by
  induction n with
  | zero => simp [iteratedPreparation,inputCalls]
  | succ n ih => simp [iteratedPreparation,inputCalls,ih,pow_succ,mul_comm]

theorem iterated_parallel_registers (k n : ℕ) : parallelRegisters (iteratedPreparation k n)=k^n := by
  induction n with
  | zero => simp [iteratedPreparation,parallelRegisters]
  | succ n ih => simp [iteratedPreparation,parallelRegisters,ih,pow_succ,mul_comm]

theorem iterated_filter_calls (k n : ℕ) :
    filterCalls (iteratedPreparation k n)=∑ j ∈ Finset.range n,k^j := by
  induction n with
  | zero => simp [iteratedPreparation,filterCalls]
  | succ n ih =>
    simp only [iteratedPreparation,filterCalls,ih,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [Finset.sum_range_succ']
    simp only [pow_zero,pow_succ,← Finset.sum_mul]
    norm_cast
    ring

def reservedBits {k : ℕ} (qubits : ℕ) (t : PreparationTree k) : ℕ := qubits*parallelRegisters t

theorem iterated_reserved_bits (k n qubits : ℕ) :
    reservedBits qubits (iteratedPreparation k n)=qubits*k^n := by
  rw [reservedBits,iterated_parallel_registers]

end Qatlib.Papers.QGradient20.CopyBudget
