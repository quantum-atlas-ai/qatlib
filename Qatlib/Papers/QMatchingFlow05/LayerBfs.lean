/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs

/-!
# Layered search cost aggregation

This module aggregates vertex-search budgets into the layered-search bounds associated with
Theorem 1 of [AmbainisSpalek2006]. The adjacency result sums uniform bounds supplied for each
vertex.

The list result uses nonnegative per-vertex discovery and degree quantities, their global sum
bounds, and the square-root summation inequality to control the total `listVertexCost`.

## Main statements

* `theorem1_adjacency`: the summed budget is bounded by a constant times `n ^ (3 / 2) *
  logFactor n`.
* `theorem1_list`: the summed list budget is bounded by a constant times `c * √(n * m) *
  logFactor n`.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.LayerBfs

open Qatlib.Papers.QMatchingFlow05.SearchTools

/-- For natural `n`, the product `n * √n` equals `n ^ (3 / 2)`. -/
theorem nat_mul_sqrt_eq_rpow (n : ℕ) :
    (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ ((3 : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [Real.sqrt_eq_rpow]
    have hsplit : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
    rw [hsplit, Real.rpow_add hn, Real.rpow_one]

/-- For nonnegative `c`, any family bounded pointwise by `adjacencyVertexCost c n` has total at
most `C * n ^ (3 / 2) * logFactor n` for some positive `C`. See [AmbainisSpalek2006]. -/
theorem theorem1_adjacency (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (perVertex : Fin n → ℝ),
      (∀ v, perVertex v ≤ adjacencyVertexCost c n) →
      (∑ v, perVertex v) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n := by
  refine ⟨2 * c + 1, by positivity, ?_⟩
  intro n perVertex hper
  have hsum : (∑ v, perVertex v) ≤ ∑ _v : Fin n, adjacencyVertexCost c n :=
    Finset.sum_le_sum fun v _ => hper v
  have hconst : (∑ _v : Fin n, adjacencyVertexCost c n) =
      (n : ℝ) * adjacencyVertexCost c n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcost : (n : ℝ) * adjacencyVertexCost c n =
      2 * c * ((n : ℝ) * Real.sqrt (n : ℝ)) * logFactor n := by
    unfold adjacencyVertexCost searchCost
    ring
  have hpow : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (logFactor_pos n).le
  calc (∑ v, perVertex v) ≤ ∑ _v : Fin n, adjacencyVertexCost c n := hsum
    _ = (n : ℝ) * adjacencyVertexCost c n := hconst
    _ = 2 * c * ((n : ℝ) * Real.sqrt (n : ℝ)) * logFactor n := hcost
    _ = 2 * c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n := by
        rw [nat_mul_sqrt_eq_rpow]
    _ ≤ (2 * c + 1) * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n := by
        nlinarith [hpow, hc]

/-- For nonnegative `c`, the stated size and global sum bounds on nonnegative `nV` and `dV`
imply a total list cost at most `C * c * √(n * m) * logFactor n` for some positive `C`. See
[AmbainisSpalek2006]. -/
theorem theorem1_list (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n m : ℕ) (nV dV : Fin k → ℝ),
      2 ≤ n → k ≤ n → n ≤ m + 1 →
      (∀ v, 0 ≤ nV v) → (∀ v, 0 ≤ dV v) →
      (∑ v, nV v) ≤ (n : ℝ) → (∑ v, dV v) ≤ (m : ℝ) →
      (∑ v, listVertexCost c (nV v) (dV v)) ≤
        C * c * Real.sqrt ((n : ℝ) * (m : ℝ)) * logFactor n := by
  refine ⟨4, by norm_num, ?_⟩
  intro k n m nV dV hn2 hkn hnm hnV hdV hsumN hsumD
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnm' : (n : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hnm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith

  have hA : (∑ v, Real.sqrt (nV v * dV v)) ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) := by
    have hcs := sum_sqrt_mul_le nV dV hnV hdV
    have hsn : Real.sqrt (∑ v, nV v) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hsumN
    have hsd : Real.sqrt (∑ v, dV v) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hsumD
    calc (∑ v, Real.sqrt (nV v * dV v))
        ≤ Real.sqrt (∑ v, nV v) * Real.sqrt (∑ v, dV v) := hcs
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul hsn hsd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((n : ℝ) * (m : ℝ)) := (Real.sqrt_mul hnpos.le (m : ℝ)).symm

  have hB : (∑ v, Real.sqrt (dV v + 1)) ≤ 2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
    have hcs := sum_sqrt_mul_le (fun v : Fin k => dV v + 1) (fun _ => (1 : ℝ))
      (fun v => by have := hdV v; linarith) (fun _ => by norm_num)
    simp only [mul_one] at hcs
    have hsumk : (∑ v : Fin k, (dV v + 1)) ≤ (m : ℝ) + (n : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      linarith
    have hkone : (∑ _v : Fin k, (1 : ℝ)) = (k : ℝ) := by simp
    rw [hkone] at hcs
    have hk_le : Real.sqrt (k : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hkn)
    have hsum_le : Real.sqrt (∑ v, (dV v + 1)) ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) :=
      Real.sqrt_le_sqrt hsumk
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hnle : (n : ℝ) ≤ 2 * (m : ℝ) := by linarith
    have hnpos' : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have hsq : (n : ℝ) * (n : ℝ) ≤ 2 * ((m : ℝ) * (n : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hnle hnpos'
      nlinarith [this]
    have hquad : ((m : ℝ) + (n : ℝ)) * (n : ℝ) ≤ 4 * ((n : ℝ) * (m : ℝ)) := by
      nlinarith [hsq, mul_nonneg hmpos.le hnpos']
    have hstep : Real.sqrt ((m : ℝ) + (n : ℝ)) * Real.sqrt (n : ℝ) ≤
        2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
      rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ (m : ℝ) + (n : ℝ)) (n : ℝ)]
      have h4 : Real.sqrt (((m : ℝ) + (n : ℝ)) * (n : ℝ)) ≤
          Real.sqrt (4 * ((n : ℝ) * (m : ℝ))) := Real.sqrt_le_sqrt hquad
      have h4f : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h4' : Real.sqrt (4 * ((n : ℝ) * (m : ℝ))) =
          2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4f]
      linarith [h4, h4'.le]
    calc (∑ v, Real.sqrt (dV v + 1))
        ≤ Real.sqrt (∑ v, (dV v + 1)) * Real.sqrt (k : ℝ) := hcs
      _ ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) * Real.sqrt (n : ℝ) :=
          mul_le_mul hsum_le hk_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := hstep
  have hsplit : (∑ v, listVertexCost c (nV v) (dV v)) =
      c * ((∑ v, Real.sqrt (nV v * dV v)) + ∑ v, Real.sqrt (dV v + 1)) := by
    calc (∑ v, listVertexCost c (nV v) (dV v))
        = ∑ v, (c * Real.sqrt (nV v * dV v) + c * Real.sqrt (dV v + 1)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          unfold listVertexCost
          ring
      _ = c * ((∑ v, Real.sqrt (nV v * dV v)) + ∑ v, Real.sqrt (dV v + 1)) := by
          rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hR : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) := Real.sqrt_nonneg _
  calc (∑ v, listVertexCost c (nV v) (dV v))
      = c * ((∑ v, Real.sqrt (nV v * dV v)) + ∑ v, Real.sqrt (dV v + 1)) := hsplit
    _ ≤ c * (Real.sqrt ((n : ℝ) * (m : ℝ)) + 2 * Real.sqrt ((n : ℝ) * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hc
    _ = 3 * c * Real.sqrt ((n : ℝ) * (m : ℝ)) := by ring
    _ ≤ 4 * c * Real.sqrt ((n : ℝ) * (m : ℝ)) * logFactor n := by
        have hprod : (0 : ℝ) ≤ c * Real.sqrt ((n : ℝ) * (m : ℝ)) := mul_nonneg hc hR
        have hl : (1 : ℝ) ≤ logFactor n := one_le_logFactor n
        have hmul := mul_le_mul_of_nonneg_left hl hprod
        nlinarith [hmul, hprod]

end Qatlib.Papers.QMatchingFlow05.LayerBfs

end
