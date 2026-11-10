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
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Finset

namespace Qatlib.Papers.QSearchAdvice09.MainResults

def roundCost (k : ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, ((⌊k ^ i⌋₊ : ℝ) + 3) / 2

theorem geom_range (k : ℝ) (hk : k ≠ 1) (j : ℕ) :
    ∑ i ∈ range j, k ^ i = (k ^ j - 1) / (k - 1) :=
  geom_sum_eq hk j

theorem prod_one_sub_le_one (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j : ℕ) : ∏ i ∈ range j, (1 - P i) ≤ 1 := by
  refine Finset.prod_le_one₀ ?_ ?_
  · intro i _
    linarith [hP0 i, hP1 i]
  · intro i _
    linarith [hP0 i]

theorem prod_decay (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j0 : ℕ) (hquarter : ∀ i, j0 ≤ i → 1 / 4 ≤ P i) :
    ∀ j : ℕ, j0 ≤ j → ∏ i ∈ range j, (1 - P i) ≤ (3 / 4) ^ (j - j0) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have := prod_one_sub_le_one P hP0 hP1 j0
    simpa using this
  | succ j hj ih =>
    rw [prod_range_succ, Nat.succ_sub hj]
    have hfactor : 1 - P j ≤ 3 / 4 := by linarith [hquarter j hj]
    have hnonneg : (0 : ℝ) ≤ 1 - P j := by linarith [hP1 j]
    have hb : (0 : ℝ) ≤ (3 / 4) ^ (j - j0) := by positivity
    calc (∏ i ∈ range j, (1 - P i)) * (1 - P j)
        ≤ (3 / 4) ^ (j - j0) * (3 / 4) := mul_le_mul ih hfactor hnonneg hb
      _ = (3 / 4) ^ ((j - j0).succ) := by rw [pow_succ]

theorem amplification_tail (P C : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j0 : ℕ) (hquarter : ∀ i, j0 ≤ i → 1 / 4 ≤ P i)
    (C0 : ℝ) (hC0 : 0 ≤ C0) (hCnn : ∀ i, 0 ≤ C i)
    (hC : ∀ t, C (j0 + t) ≤ C0 * (3 / 4) ^ t) (s : ℕ) :
    ∑ t ∈ range s, (∏ i ∈ range (j0 + t), (1 - P i)) * P (j0 + t) * C (j0 + t)
      ≤ (16 / 7) * C0 := by
  have hterm : ∀ t ∈ range s,
      (∏ i ∈ range (j0 + t), (1 - P i)) * P (j0 + t) * C (j0 + t)
        ≤ C0 * ((3 / 4) ^ t * (3 / 4) ^ t) := by
    intro t _
    have hprod := prod_decay P hP0 hP1 j0 hquarter (j0 + t) (Nat.le_add_right j0 t)
    have hsub : j0 + t - j0 = t := Nat.add_sub_cancel_left j0 t
    rw [hsub] at hprod
    have hPle : P (j0 + t) ≤ 1 := hP1 _
    have hPnn : 0 ≤ P (j0 + t) := hP0 _
    have hCnn' : 0 ≤ C (j0 + t) := hCnn _
    calc (∏ i ∈ range (j0 + t), (1 - P i)) * P (j0 + t) * C (j0 + t)
        ≤ (3 / 4) ^ t * 1 * C (j0 + t) := by
          exact mul_le_mul (mul_le_mul hprod hPle hPnn (by positivity)) le_rfl
            hCnn' (by positivity)
      _ ≤ (3 / 4) ^ t * 1 * (C0 * (3 / 4) ^ t) := by
          exact mul_le_mul_of_nonneg_left (hC t) (by positivity)
      _ = C0 * ((3 / 4) ^ t * (3 / 4) ^ t) := by ring
  calc ∑ t ∈ range s, (∏ i ∈ range (j0 + t), (1 - P i)) * P (j0 + t) * C (j0 + t)
      ≤ ∑ t ∈ range s, C0 * ((3 / 4) ^ t * (3 / 4) ^ t) := sum_le_sum hterm
    _ = C0 * ∑ t ∈ range s, ((3 / 4) * (3 / 4)) ^ t := by
        rw [← mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun t _ => by rw [mul_pow]
    _ ≤ C0 * (1 / (1 - (3 / 4 : ℝ) * (3 / 4))) := by
        have hr0 : (0 : ℝ) ≤ (3 / 4 : ℝ) * (3 / 4) := by norm_num
        have hr1 : (3 / 4 : ℝ) * (3 / 4) < 1 := by norm_num
        have hgeo : ∑ t ∈ range s, ((3 / 4 : ℝ) * (3 / 4)) ^ t
            ≤ 1 / (1 - (3 / 4 : ℝ) * (3 / 4)) := by
          have h := geom_sum_eq (x := (3 / 4 : ℝ) * (3 / 4)) (ne_of_lt hr1) s
          have hnonneg : (0 : ℝ) ≤ ((3 / 4 : ℝ) * (3 / 4)) ^ s := pow_nonneg hr0 s
          have hle1 : ((3 / 4 : ℝ) * (3 / 4)) ^ s ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
          have hden : (0 : ℝ) < 1 - (3 / 4 : ℝ) * (3 / 4) := by norm_num
          have hEq : (((3 / 4 : ℝ) * (3 / 4)) ^ s - 1) / ((3 / 4 : ℝ) * (3 / 4) - 1)
              = (1 - ((3 / 4 : ℝ) * (3 / 4)) ^ s) / (1 - (3 / 4 : ℝ) * (3 / 4)) := by
            field_simp
            ring
          rw [h, hEq]
          exact (div_le_div_iff_of_pos_right hden).mpr (by nlinarith [hnonneg])
        exact mul_le_mul_of_nonneg_left hgeo hC0
    _ = (16 / 7) * C0 := by
        have h : (1 : ℝ) - (3 / 4) * (3 / 4) = 7 / 16 := by norm_num
        rw [h]
        field_simp

end Qatlib.Papers.QSearchAdvice09.MainResults
