/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs

/-!
# Network flow resource bounds from blocking costs

This module develops the scalar blocking-flow resource bounds for Theorem 6 of
[AmbainisSpalek2006]. It proves power identities, a depth estimate, and a summation estimate
controlling the square-root phase terms.

The main inequalities use the specified positive cutoff `k` and the hypothesis `k * U ≤ n` to
derive list-model and adjacency-model budgets. The latter includes the capacity restriction `U ≤
n ^ (1 / 4)`.

## Main statements

* `flowDepthBound`: a capacity-dependent cutoff obeys the depth budget.
* `theorem6_blockSum`: bounds a sum of square-root phase terms.
* `theorem6_list`: the list-model aggregate resource inequality.
* `theorem6_adjacency`: the adjacency-model aggregate resource inequality.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.BlockingFlow

open Qatlib.Papers.QMatchingFlow05.SearchTools

/-- For positive `k`, one has `k ^ (3 / 2) = k * √k`. -/
theorem rpow_three_halves_eq (k : ℝ) (hk : 0 < k) :
    k ^ ((3 : ℝ) / 2) = k * Real.sqrt k := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hk, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- For positive `n`, one has `n ^ (2 / 3) * √n = n ^ (7 / 6)`. -/
theorem rpow_seven_sixths (n : ℝ) (hn : 0 < n) :
    n ^ ((2 : ℝ) / 3) * Real.sqrt n = n ^ ((7 : ℝ) / 6) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn, show ((2 : ℝ) / 3 + 1 / 2) = 7 / 6 by norm_num]

/-- For positive `n`, one has `n ^ (2 / 3) * n ^ (3 / 2) = n ^ (13 / 6)`. -/
theorem rpow_thirteen_sixths (n : ℝ) (hn : 0 < n) :
    n ^ ((2 : ℝ) / 3) * n ^ ((3 : ℝ) / 2) = n ^ ((13 : ℝ) / 6) := by
  rw [← Real.rpow_add hn, show ((2 : ℝ) / 3 + 3 / 2) = 13 / 6 by norm_num]

/-- For positive `n` and `U` with `U ≤ n ^ (1 / 4)`, the cutoff `min (n ^ (2 / 3) * U ^ (1 / 3))
(√(m * U))`, multiplied by `U`, is at most `n`. See [AmbainisSpalek2006]. -/
theorem flowDepthBound (n U m : ℝ) (hn : 0 < n) (hU : 0 < U)
    (hUq : U ≤ n ^ ((1 : ℝ) / 4)) :
    min (n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) (Real.sqrt (m * U)) * U ≤ n := by
  have hbranch : n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) * U ≤ n := by
    have hU4 : U ^ ((4 : ℝ) / 3) ≤ n ^ ((1 : ℝ) / 3) := by
      have h1 : U ^ ((4 : ℝ) / 3) ≤ (n ^ ((1 : ℝ) / 4)) ^ ((4 : ℝ) / 3) :=
        Real.rpow_le_rpow hU.le hUq (by norm_num)
      have h2 : (n ^ ((1 : ℝ) / 4)) ^ ((4 : ℝ) / 3) = n ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_mul hn.le ((1 : ℝ) / 4) ((4 : ℝ) / 3)]
        norm_num
      linarith [h1, h2.le, h2.ge]
    have hsplit : n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) * U =
        n ^ ((2 : ℝ) / 3) * U ^ ((4 : ℝ) / 3) := by
      rw [show U ^ ((4 : ℝ) / 3) = U ^ ((1 : ℝ) / 3) * U by
        rw [show ((4 : ℝ) / 3) = 1 / 3 + 1 by norm_num, Real.rpow_add hU, Real.rpow_one]]
      ring
    calc n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) * U
        = n ^ ((2 : ℝ) / 3) * U ^ ((4 : ℝ) / 3) := hsplit
      _ ≤ n ^ ((2 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hU4 (Real.rpow_nonneg hn.le _)
      _ = n := by
          rw [← Real.rpow_add hn, show ((2 : ℝ) / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
  calc min (n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) (Real.sqrt (m * U)) * U
      ≤ n ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) * U :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hU.le
    _ ≤ n := hbranch

/-- If `k > 0`, `m ≥ 0`, `U > 0`, `n ≥ 0`, and `k * U ≤ n`, then `k ^ (3 / 2) * √(m * U) ≤ k *
√(n * m)`. See [AmbainisSpalek2006]. -/
theorem blockingFlow_le_singlePath (n m U k : ℝ) (hk : 0 < k) (hm : 0 ≤ m)
    (_hU : 0 < U) (hkU : k * U ≤ n) (hn : 0 ≤ n) :
    k ^ ((3 : ℝ) / 2) * Real.sqrt (m * U) ≤ k * Real.sqrt (n * m) := by
  have hkU' : Real.sqrt (k * U) ≤ Real.sqrt n := Real.sqrt_le_sqrt hkU
  have hsqrt : Real.sqrt (k * U) = Real.sqrt k * Real.sqrt U := Real.sqrt_mul hk.le U
  rw [hsqrt] at hkU'
  rw [rpow_three_halves_eq k hk, Real.sqrt_mul hm U, Real.sqrt_mul hn m]
  have hkm : (0 : ℝ) ≤ k * Real.sqrt m := mul_nonneg hk.le (Real.sqrt_nonneg _)
  calc k * Real.sqrt k * (Real.sqrt m * Real.sqrt U)
      = (k * Real.sqrt m) * (Real.sqrt k * Real.sqrt U) := by ring
    _ ≤ (k * Real.sqrt m) * Real.sqrt n := mul_le_mul_of_nonneg_left hkU' hkm
    _ = k * (Real.sqrt n * Real.sqrt m) := by ring

/-- For nonnegative `c`, nonnegative terms with sum at most `c * k` satisfy `∑ j ∈ Icc 1 k, √(j
* A j) ≤ C * (c + 1) * k * √k` for some positive `C`. See [AmbainisSpalek2006]. -/
theorem theorem6_blockSum (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (A : ℕ → ℝ), (∀ j, 0 ≤ A j) →
      (∑ j ∈ Finset.Icc 1 k, A j) ≤ c * (k : ℝ) →
      (∑ j ∈ Finset.Icc 1 k, Real.sqrt ((j : ℝ) * A j)) ≤
        C * (c + 1) * ((k : ℝ) * Real.sqrt (k : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro k A hA hsum
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k

  have hsumj : (∑ j ∈ Finset.Icc 1 k, (j : ℝ)) ≤ (k : ℝ) ^ 2 := by
    have hstep : (∑ j ∈ Finset.Icc 1 k, (j : ℝ)) ≤ ∑ _j ∈ Finset.Icc 1 k, (k : ℝ) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      exact_mod_cast hjk
    rw [Finset.sum_const, nsmul_eq_mul] at hstep
    have hcard : ((Finset.Icc 1 k).card : ℝ) = (k : ℝ) := by
      rw [Nat.card_Icc]
      simp
    rw [hcard] at hstep
    calc (∑ j ∈ Finset.Icc 1 k, (j : ℝ)) ≤ (k : ℝ) * (k : ℝ) := hstep
      _ = (k : ℝ) ^ 2 := by ring
  have hsqrt_eq : (∑ j ∈ Finset.Icc 1 k, Real.sqrt ((j : ℝ) * A j)) =
      ∑ j ∈ Finset.Icc 1 k, Real.sqrt (j : ℝ) * Real.sqrt (A j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sqrt_mul (Nat.cast_nonneg j) (A j)]
  rw [hsqrt_eq]
  have hcs := Real.sum_sqrt_mul_sqrt_le (s := Finset.Icc 1 k)
    (f := fun j : ℕ => (j : ℝ)) (g := A) (fun j => Nat.cast_nonneg j) hA
  have hsumA : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 k, A j :=
    Finset.sum_nonneg fun j _ => hA j
  have hck : (0 : ℝ) ≤ c * (k : ℝ) := mul_nonneg hc hk0
  calc (∑ j ∈ Finset.Icc 1 k, Real.sqrt (j : ℝ) * Real.sqrt (A j))
      ≤ Real.sqrt (∑ j ∈ Finset.Icc 1 k, (j : ℝ)) *
          Real.sqrt (∑ j ∈ Finset.Icc 1 k, A j) := hcs
    _ ≤ Real.sqrt ((k : ℝ) ^ 2) * Real.sqrt (c * (k : ℝ)) :=
        mul_le_mul (Real.sqrt_le_sqrt hsumj) (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = (k : ℝ) * Real.sqrt (c * (k : ℝ)) := by rw [Real.sqrt_sq hk0]
    _ = (k : ℝ) * (Real.sqrt c * Real.sqrt (k : ℝ)) := by rw [Real.sqrt_mul hc]
    _ ≤ (k : ℝ) * ((c + 1) * Real.sqrt (k : ℝ)) := by
        have hsc : Real.sqrt c ≤ c + 1 := by
          nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]
        have := mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg (k : ℝ))
        exact mul_le_mul_of_nonneg_left this hk0
    _ = 1 * (c + 1) * ((k : ℝ) * Real.sqrt (k : ℝ)) := by ring

/-- Under the specified positive cutoff and depth hypotheses, the aggregate blocking cost is at
most `C * min (n ^ (7 / 6) * √m * U ^ (1 / 3)) (√(n * U) * m) * logFactor n` for some
positive `C`. See [AmbainisSpalek2006]. -/
theorem theorem6_list (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (U k : ℝ), 2 ≤ n → 0 < U →
      k = min ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) (Real.sqrt ((m : ℝ) * U)) →
      0 < k → k * U ≤ (n : ℝ) →
      c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
          k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
        C * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
          (Real.sqrt ((n : ℝ) * U) * (m : ℝ)) * logFactor n := by
  refine ⟨2 * (c + 1), by positivity, ?_⟩
  intro n m U k hn2 hU hkdef hk hkU
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnm : (0 : ℝ) ≤ (n : ℝ) * (m : ℝ) := mul_nonneg hn0 hm0
  have hmU : (0 : ℝ) ≤ (m : ℝ) * U := mul_nonneg hm0 hU.le

  have hmain : k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) ≤
      k * Real.sqrt ((n : ℝ) * (m : ℝ)) :=
    blockingFlow_le_singlePath (n : ℝ) (m : ℝ) U k hk hm0 hU hkU hn0

  have hB1 : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
      (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3) := by
    have hkle : k ≤ (n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) := by
      rw [hkdef]; exact min_le_left _ _
    have hstep : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
        ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) *
          (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by
      rw [Real.sqrt_mul hn0 (m : ℝ)]
      exact mul_le_mul_of_nonneg_right hkle (by positivity)
    calc k * Real.sqrt ((n : ℝ) * (m : ℝ))
        ≤ ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) *
            (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := hstep
      _ = ((n : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt (n : ℝ)) * U ^ ((1 : ℝ) / 3) *
            Real.sqrt (m : ℝ) := by ring
      _ = (n : ℝ) ^ ((7 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) * Real.sqrt (m : ℝ) := by
          rw [rpow_seven_sixths (n : ℝ) hnpos]
      _ = (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3) := by ring
  have hB2 : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
      Real.sqrt ((n : ℝ) * U) * (m : ℝ) := by
    have hkle : k ≤ Real.sqrt ((m : ℝ) * U) := by
      rw [hkdef]; exact min_le_right _ _
    have hstep : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
        Real.sqrt ((m : ℝ) * U) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by
      rw [Real.sqrt_mul hn0 (m : ℝ)]
      exact mul_le_mul_of_nonneg_right hkle (by positivity)
    calc k * Real.sqrt ((n : ℝ) * (m : ℝ))
        ≤ Real.sqrt ((m : ℝ) * U) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := hstep
      _ = (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) *
            (Real.sqrt U * Real.sqrt (n : ℝ)) := by
          rw [Real.sqrt_mul hm0 U]; ring
      _ = (m : ℝ) * Real.sqrt (U * (n : ℝ)) := by
          rw [Real.mul_self_sqrt hm0, Real.sqrt_mul hU.le (n : ℝ)]
      _ = (m : ℝ) * Real.sqrt ((n : ℝ) * U) := by rw [mul_comm U (n : ℝ)]
      _ = Real.sqrt ((n : ℝ) * U) * (m : ℝ) := by ring
  have hbound : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
      min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
        (Real.sqrt ((n : ℝ) * U) * (m : ℝ)) := le_min hB1 hB2

  have hsum : k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
      k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤ 2 * (k * Real.sqrt ((n : ℝ) * (m : ℝ))) := by
    linarith [hmain]
  have hlog : (1 : ℝ) ≤ logFactor n := one_le_logFactor n
  have hmin0 : (0 : ℝ) ≤ min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
      (Real.sqrt ((n : ℝ) * U) * (m : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3) := by
      have := Real.rpow_nonneg hn0 ((7 : ℝ) / 6)
      have := Real.rpow_nonneg hU.le ((1 : ℝ) / 3)
      positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * U) * (m : ℝ) := by positivity
    exact le_min h1 h2
  have hc0 : (0 : ℝ) ≤ c := hc
  have hstep1 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
      k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤ c * (2 * (k * Real.sqrt ((n : ℝ) * (m : ℝ)))) :=
    mul_le_mul_of_nonneg_left hsum hc0
  have hstep2 : c * (2 * (k * Real.sqrt ((n : ℝ) * (m : ℝ)))) ≤
      c * (2 * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
        (Real.sqrt ((n : ℝ) * U) * (m : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_left this hc0
  have hstep3 : c * (2 * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
      (Real.sqrt ((n : ℝ) * U) * (m : ℝ))) ≤
      2 * (c + 1) * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ^ ((1 : ℝ) / 3))
        (Real.sqrt ((n : ℝ) * U) * (m : ℝ)) * logFactor n := by
    have hmul := mul_le_mul_of_nonneg_left hlog hmin0
    nlinarith [hmin0, hmul, hc0]
  exact le_trans hstep1 (le_trans hstep2 hstep3)

/-- With the stated cutoff, depth, and capacity hypotheses, the adjacency-model aggregate cost
is at most `C * n ^ (13 / 6) * U ^ (1 / 3) * logFactor n` for some positive `C`. See
[AmbainisSpalek2006]. -/
theorem theorem6_adjacency (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (U k : ℝ), 2 ≤ n → 0 < U → U ≤ (n : ℝ) ^ ((1 : ℝ) / 4) →
      k = min ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3))
        (Real.sqrt ((n : ℝ) ^ 2 * U)) →
      0 < k → k * U ≤ (n : ℝ) →
      c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((n : ℝ) ^ 2 * U) +
          k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2)) ≤
        C * (n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) * logFactor n := by
  refine ⟨2 * (c + 1), by positivity, ?_⟩
  intro n U k hn2 hU hUq hkdef hk hkU
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le

  have hmain : k ^ ((3 : ℝ) / 2) * Real.sqrt ((n : ℝ) ^ 2 * U) ≤
      k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2) :=
    blockingFlow_le_singlePath (n : ℝ) ((n : ℝ) ^ 2) U k hk (by positivity) hU hkU hn0

  have hB : k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2) ≤
      (n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) := by
    have hkle : k ≤ (n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3) := by
      rw [hkdef]; exact min_le_left _ _
    have hroot : Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2) = (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [show (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 by ring, ← Real.rpow_natCast (n : ℝ) 3,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
      norm_num
    have hstep : k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2) ≤
        ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [hroot]
      exact mul_le_mul hkle le_rfl (Real.rpow_nonneg hn0 _) (by positivity)
    calc k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2)
        ≤ ((n : ℝ) ^ ((2 : ℝ) / 3) * U ^ ((1 : ℝ) / 3)) * (n : ℝ) ^ ((3 : ℝ) / 2) := hstep
      _ = ((n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((3 : ℝ) / 2)) * U ^ ((1 : ℝ) / 3) := by ring
      _ = (n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) := by
          rw [rpow_thirteen_sixths (n : ℝ) hnpos]
  have hsum : k ^ ((3 : ℝ) / 2) * Real.sqrt ((n : ℝ) ^ 2 * U) +
      k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2) ≤
      2 * ((n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3)) := by linarith [hmain, hB]
  have hlog : (1 : ℝ) ≤ logFactor n := one_le_logFactor n
  have hB0 : (0 : ℝ) ≤ (n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) := by
    have := Real.rpow_nonneg hn0 ((13 : ℝ) / 6)
    have := Real.rpow_nonneg hU.le ((1 : ℝ) / 3)
    positivity
  have hstep1 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((n : ℝ) ^ 2 * U) +
      k * Real.sqrt ((n : ℝ) * (n : ℝ) ^ 2)) ≤
      c * (2 * ((n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3))) :=
    mul_le_mul_of_nonneg_left hsum hc
  have hstep2 : c * (2 * ((n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3))) ≤
      2 * (c + 1) * (n : ℝ) ^ ((13 : ℝ) / 6) * U ^ ((1 : ℝ) / 3) * logFactor n := by
    have hmul := mul_le_mul_of_nonneg_left hlog hB0
    nlinarith [hB0, hmul, hc]
  exact le_trans hstep1 hstep2

end Qatlib.Papers.QMatchingFlow05.BlockingFlow

end
