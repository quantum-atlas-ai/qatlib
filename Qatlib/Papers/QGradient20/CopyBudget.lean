/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Copy expansion in iterated preparation trees

`PreparationTree` models input preparations and filters with `k` children. The full depth-`n`
tree has `k^n` input calls and parallel registers, a geometric sum of filter calls, and the
corresponding reserved-bit count; these are counts for the specified tree model. The
mathematical context is [GaoEtAl2021].

## Main statements

* `iterated_input_calls`: The full `k`-ary preparation tree of depth `n` makes `k^n` input
  calls.
* `iterated_filter_calls`: The full depth-`n` preparation tree has `∑ j ∈ range n, k^j` filter
  calls.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QGradient20.CopyBudget

/-- A preparation tree with input leaves and filter nodes indexed by `Fin k`. -/
inductive PreparationTree (k : ℕ) where
  | input : PreparationTree k
  | filter : (Fin k → PreparationTree k) → PreparationTree k

/-- Count input leaves recursively, summing across the children of each filter node. -/
def inputCalls {k : ℕ} : PreparationTree k → ℕ
  | .input => 1
  | .filter children => ∑ i, inputCalls (children i)

/-- Count filter nodes recursively, adding one at each filter and summing its child counts. -/
def filterCalls {k : ℕ} : PreparationTree k → ℕ
  | .input => 0
  | .filter children => 1 + ∑ i, filterCalls (children i)

/-- Count the recursively reserved input registers by summing across filter children. -/
def parallelRegisters {k : ℕ} : PreparationTree k → ℕ
  | .input => 1
  | .filter children => ∑ i, parallelRegisters (children i)

/-- The full `k`-ary preparation tree of depth `n`, with an input leaf at depth zero. -/
def iteratedPreparation (k : ℕ) : ℕ → PreparationTree k
  | 0 => .input
  | n+1 => .filter (fun _ => iteratedPreparation k n)

/-- The full `k`-ary preparation tree of depth `n` makes `k^n` input calls. See [GaoEtAl2021]. -/
theorem iterated_input_calls (k n : ℕ) : inputCalls (iteratedPreparation k n)=k^n := by
  induction n with
  | zero => simp [iteratedPreparation,inputCalls]
  | succ n ih => simp [iteratedPreparation,inputCalls,ih,pow_succ,mul_comm]

/-- The full `k`-ary preparation tree of depth `n` reserves `k^n` parallel registers. -/
theorem iterated_parallel_registers (k n : ℕ) : parallelRegisters (iteratedPreparation k n)=k^n := by
  induction n with
  | zero => simp [iteratedPreparation,parallelRegisters]
  | succ n ih => simp [iteratedPreparation,parallelRegisters,ih,pow_succ,mul_comm]

/-- The full depth-`n` preparation tree has `∑ j ∈ range n, k^j` filter calls. See
[GaoEtAl2021]. -/
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

/-- The qubit count per register multiplied by the tree's parallel-register count. -/
def reservedBits {k : ℕ} (qubits : ℕ) (t : PreparationTree k) : ℕ := qubits*parallelRegisters t

/-- With `qubits` bits per register, the full depth-`n` preparation tree reserves `qubits * k^n`
bits. See [GaoEtAl2021]. -/
theorem iterated_reserved_bits (k n qubits : ℕ) :
    reservedBits qubits (iteratedPreparation k n)=qubits*k^n := by
  rw [reservedBits,iterated_parallel_registers]

end Qatlib.Papers.QGradient20.CopyBudget
