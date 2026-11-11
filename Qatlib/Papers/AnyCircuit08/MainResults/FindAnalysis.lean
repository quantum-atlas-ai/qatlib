/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Recurrence and repetition estimates for FIND

The recurrence `findQ` has a geometric-sum expression and a polynomial bound when the recursion
depth is logarithmic in the input parameter. The module also gives scalar failure and success
estimates at the logarithmic repetition threshold used in the FIND analysis
[HallgrenHarrow2008].

## Main statements

* `findQ_eq_sum`: expresses the query recurrence as a geometric sum.
* `findQ_polynomial`: bounds the recurrence under `2 ^ ℓ ≤ n`.
* `find_failure_amplitude`: bounds the square root of the repetition failure expression.

## References

* [Hallgren and Harrow, 2008][HallgrenHarrow2008]
-/

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

/-- Every natural number `n` satisfies `n ≤ 2 ^ n`. -/
theorem le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      have ih : n ≤ 2 ^ n := le_two_pow n
      have h2 : (1 : ℕ) ≤ 2 ^ n := by
        have hpos := pow_pos (by norm_num : (0:ℕ) < 2) n
        omega
      calc n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left h2 _
        _ = 2 * 2 ^ n := by ring
        _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- The query-count recurrence with initial value zero and step `findQ m (j + 1) = 2 * m * findQ
m j + 2 * m`. -/
def findQ (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * m * findQ m j + 2 * m

/-- The successor value of `findQ` equals `2 * m * findQ m j + 2 * m`. -/
theorem findQ_succ (m j : ℕ) : findQ m (j + 1) = 2 * m * findQ m j + 2 * m := rfl

/-- The value `findQ m j` is the sum of `(2 * m) ^ (i + 1)` for `i < j` [HallgrenHarrow2008]. -/
theorem findQ_eq_sum (m : ℕ) : ∀ j : ℕ,
    findQ m j = ∑ i ∈ Finset.range j, (2 * m) ^ (i + 1)
  | 0 => by simp [findQ]
  | j + 1 => by
      rw [findQ_succ, findQ_eq_sum m j, Finset.mul_sum, Finset.sum_range_succ']
      have hterm : ∀ i ∈ Finset.range j,
          2 * m * (2 * m) ^ (i + 1) = (2 * m) ^ (i + 1 + 1) := by
        intro i _
        exact (pow_succ' (2 * m) (i + 1)).symm
      rw [Finset.sum_congr rfl hterm]
      simp

/-- For `m ≥ 1`, the recurrence `findQ m j` is bounded by `(2 * m) ^ (j + 1)`. -/
theorem findQ_le_pow (m : ℕ) (hm : 1 ≤ m) (j : ℕ) :
    findQ m j ≤ (2 * m) ^ (j + 1) := by
  rw [findQ_eq_sum]
  have ha : 2 ≤ 2 * m := by omega
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ]
      calc (∑ i ∈ Finset.range j, (2 * m) ^ (i + 1)) + (2 * m) ^ (j + 1)
          ≤ (2 * m) ^ (j + 1) + (2 * m) ^ (j + 1) := Nat.add_le_add_right ih _
        _ = 2 * (2 * m) ^ (j + 1) := by ring
        _ ≤ (2 * m) * (2 * m) ^ (j + 1) := Nat.mul_le_mul_right _ ha
        _ = (2 * m) ^ (j + 1 + 1) := (pow_succ' (2 * m) (j + 1)).symm

/-- For `m ≥ 1` and `2 ^ ℓ ≤ n`, the recurrence satisfies `findQ m ℓ ≤ 2 * m * n ^ (2 * m)`
[HallgrenHarrow2008]. -/
theorem findQ_polynomial (m ℓ n : ℕ) (hm : 1 ≤ m) (hℓ : 2 ^ ℓ ≤ n) :
    findQ m ℓ ≤ 2 * m * n ^ (2 * m) := by
  have hbase := findQ_le_pow m hm ℓ
  have hpow : (2 * m) ^ ℓ ≤ n ^ (2 * m) := by
    have h1 : 2 * m ≤ 2 ^ (2 * m) := le_two_pow (2 * m)
    calc (2 * m) ^ ℓ ≤ (2 ^ (2 * m)) ^ ℓ := Nat.pow_le_pow_left h1 ℓ
      _ = (2 ^ ℓ) ^ (2 * m) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ n ^ (2 * m) := Nat.pow_le_pow_left hℓ _
  calc findQ m ℓ ≤ (2 * m) ^ (ℓ + 1) := hbase
    _ = 2 * m * (2 * m) ^ ℓ := by rw [pow_succ']
    _ ≤ 2 * m * n ^ (2 * m) := Nat.mul_le_mul_left _ hpow

/-- For `0 < δ ≤ 1`, the logarithmic repetition threshold bounds the square root of `(1 - δ / 2)
^ m` by `δ / 8` [HallgrenHarrow2008]. -/
theorem find_failure_amplitude (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (m : ℕ)
    (hm : (4 / δ) * Real.log (8 / δ) ≤ (m : ℝ)) :
    Real.sqrt ((1 - δ / 2) ^ m) ≤ δ / 8 := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hbase_nonneg : 0 ≤ 1 - δ / 2 := by linarith
  have hbase : 1 - δ / 2 ≤ Real.exp (-(δ / 2)) := Real.one_sub_le_exp_neg (δ / 2)
  have hpow : (1 - δ / 2) ^ m ≤ (Real.exp (-(δ / 2))) ^ m :=
    pow_le_pow_left₀ hbase_nonneg hbase m
  have hexp : (Real.exp (-(δ / 2))) ^ m = Real.exp (-((m : ℝ) * (δ / 2))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hmul : (4 / δ) * Real.log (8 / δ) * (δ / 2) = 2 * Real.log (8 / δ) := by
    field_simp
    ring
  have hprod : 2 * Real.log (8 / δ) ≤ (m : ℝ) * (δ / 2) := by
    calc 2 * Real.log (8 / δ) = (4 / δ) * Real.log (8 / δ) * (δ / 2) := hmul.symm
      _ ≤ (m : ℝ) * (δ / 2) := mul_le_mul_of_nonneg_right hm (le_of_lt hδ2)
  have hexp_le : Real.exp (-((m : ℝ) * (δ / 2))) ≤ Real.exp (-(2 * Real.log (8 / δ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hval : Real.exp (-(2 * Real.log (8 / δ))) = (δ / 8) ^ 2 := by
    have hlogeq : Real.log (8 / δ) = -Real.log (δ / 8) := by
      rw [show (8:ℝ) / δ = (δ / 8)⁻¹ by field_simp]
      rw [Real.log_inv]
    rw [hlogeq]
    have hexp2 : (-(2 * (-Real.log (δ / 8))) : ℝ) = (2:ℕ) * Real.log (δ / 8) := by
      ring
    rw [hexp2, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hsquares : (1 - δ / 2) ^ m ≤ (δ / 8) ^ 2 := by
    calc (1 - δ / 2) ^ m ≤ (Real.exp (-(δ / 2))) ^ m := hpow
      _ = Real.exp (-((m : ℝ) * (δ / 2))) := hexp
      _ ≤ Real.exp (-(2 * Real.log (8 / δ))) := hexp_le
      _ = (δ / 8) ^ 2 := hval
  have h8 : 0 ≤ δ / 8 := by positivity
  calc Real.sqrt ((1 - δ / 2) ^ m) ≤ Real.sqrt ((δ / 8) ^ 2) := Real.sqrt_le_sqrt hsquares
    _ = δ / 8 := Real.sqrt_sq h8

/-- For `0 < δ ≤ 1`, the logarithmic repetition threshold gives `1 - (1 - δ / 2) ^ m ≥ 1 - (δ /
8) ^ 2` [HallgrenHarrow2008]. -/
theorem find_level_success (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ)
    (hm : (4 / δ) * Real.log (8 / δ) ≤ (m : ℝ)) :
    1 - (1 - δ / 2) ^ m ≥ 1 - (δ / 8) ^ 2 := by
  have h := find_failure_amplitude δ hδ0 hδ1 m hm
  have hbase_nonneg : 0 ≤ 1 - δ / 2 := by linarith
  have hxnonneg : (0:ℝ) ≤ (1 - δ / 2) ^ m := pow_nonneg hbase_nonneg m
  have hsq : (1 - δ / 2) ^ m ≤ (δ / 8) ^ 2 := by
    calc (1 - δ / 2) ^ m = (Real.sqrt ((1 - δ / 2) ^ m)) ^ 2 :=
          (Real.sq_sqrt hxnonneg).symm
      _ ≤ (δ / 8) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  linarith

/-- For `0 < δ ≤ 1`, subtracting `4 * sqrt ((δ / 8) ^ 2)` from `δ` leaves at least `δ / 2`
[HallgrenHarrow2008]. -/
theorem find_success_amplitude (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) :
    δ - 4 * Real.sqrt ((δ / 8) ^ 2) ≥ δ / 2 := by
  have h8 : 0 ≤ δ / 8 := by positivity
  rw [Real.sqrt_sq h8]
  linarith

/-- For `0 < δ ≤ 1`, a nonnegative error at most `(δ / 8) ^ 2` has square root at most `δ / 8`
[HallgrenHarrow2008]. -/
theorem find_error_step (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (ε' : ℝ) (_hε'0 : 0 ≤ ε')
    (hε' : ε' ≤ (δ / 8) ^ 2) :
    Real.sqrt ε' ≤ δ / 8 := by
  have h8 : 0 ≤ δ / 8 := by positivity
  calc Real.sqrt ε' ≤ Real.sqrt ((δ / 8) ^ 2) := Real.sqrt_le_sqrt hε'
    _ = δ / 8 := Real.sqrt_sq h8

end Qatlib.Papers.AnyCircuit08.MainResults
