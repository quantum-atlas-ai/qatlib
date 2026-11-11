/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Telescoping bounds for weighted search costs

`prefixSum` and `searchTerm` encode the cumulative masses and weighted inverse-square-root terms
in the descent cost analysis. A one-step square-root inequality telescopes to bound their sum by
`2 / sqrt (popt q)`, giving the corresponding scaled query estimate.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `searchSum_bound`: For nonnegative weights with `q 0 > 0` and `n ≥ 1`, the sum of search terms
  over `[1, n)` is at most `2 / sqrt (popt q)`.
* `expected_queries_bound`: For positive `C`, nonnegative `N` and weights, positive optimal
  mass, and `n ≥ 1`, the weighted search sum multiplied by `2 * C * N` is at most `4 * C * N /
  sqrt (popt q)`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.QAOAScaling23.WeightedCost

/-- The sum of the weights `q j` for natural indices `j < k`. -/
noncomputable def prefixSum (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, q j

/-- The term `q j / (prefixSum q (j + 1) * sqrt (prefixSum q j))` in the weighted search-cost
sum. -/
noncomputable def searchTerm (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  q j / (prefixSum q (j + 1) * Real.sqrt (prefixSum q j))

/-- The weight `q 0` of the optimal rank. -/
noncomputable def popt (q : ℕ → ℝ) : ℝ := q 0

/-- The sum of successive differences `f j - f (j + 1)` over `[a, b)` equals `f a - f b` when `a
≤ b`. -/
theorem telescope (f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (f j - f (j + 1)) = f a - f b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by ring]
    rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]
    ring

/-- For `0 < a ≤ b`, `(b - a) / (b * sqrt a)` is at most `2 * (1 / sqrt a - 1 / sqrt b)`. -/
theorem step_ineq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / (b * Real.sqrt a) ≤ 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
  have hP : 0 < b * Real.sqrt a := by positivity
  rw [div_le_iff₀ hP]
  have hkey : 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) * (b * Real.sqrt a)
      = 2 * b - 2 * Real.sqrt a * Real.sqrt b := by
    field_simp
    nlinarith [hsb2]
  rw [hkey]
  have hsab : Real.sqrt a * Real.sqrt b ≤ b := by
    have : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
    nlinarith [hsa, hsb, this, hsb2]
  have hnonneg : 0 ≤ (Real.sqrt b - Real.sqrt a) ^ 2 := sq_nonneg _
  nlinarith [hsab, hnonneg, hsa2, hsb2]

/-- The prefix mass at one equals the weight at rank zero. -/
theorem prefixSum_one (q : ℕ → ℝ) : prefixSum q 1 = q 0 := by
  simp [prefixSum]

/-- For nonnegative weights with `q 0 > 0` and `n ≥ 1`, the sum of search terms over `[1, n)` is
at most `2 / sqrt (popt q)`. -/
theorem searchSum_bound (q : ℕ → ℝ) (h0 : 0 < q 0) (hnn : ∀ i, 0 ≤ q i)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, searchTerm q j ≤ 2 / Real.sqrt (popt q) := by
  have prefix_pos : ∀ k, 1 ≤ k → 0 < prefixSum q k := by
    intro k hk
    have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have hle : q 0 ≤ prefixSum q k := by
      apply Finset.single_le_sum
      · intro i _
        exact hnn i
      · exact hmem
    exact lt_of_lt_of_le h0 hle
  have prefix_mono : ∀ k, prefixSum q k ≤ prefixSum q (k + 1) := by
    intro k
    have hsucc : prefixSum q (k + 1) = prefixSum q k + q k := by
      rw [prefixSum, prefixSum, Finset.sum_range_succ]
    rw [hsucc]; linarith [hnn k]
  have hqsub : ∀ j, q j = prefixSum q (j + 1) - prefixSum q j := by
    intro j
    have hsucc : prefixSum q (j + 1) = prefixSum q j + q j := by
      rw [prefixSum, prefixSum, Finset.sum_range_succ]
    linarith
  have hstep : ∀ j ∈ Finset.Ico 1 n,
      searchTerm q j ≤ 2 * (1 / Real.sqrt (prefixSum q j)
        - 1 / Real.sqrt (prefixSum q (j + 1))) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have ha : 0 < prefixSum q j := prefix_pos j hj1
    have hab : prefixSum q j ≤ prefixSum q (j + 1) := prefix_mono j
    have hst : searchTerm q j =
        (prefixSum q (j + 1) - prefixSum q j)
          / (prefixSum q (j + 1) * Real.sqrt (prefixSum q j)) := by
      rw [searchTerm, hqsub j]
    rw [hst]
    exact step_ineq ha hab
  have hbound := Finset.sum_le_sum hstep
  have htel : ∑ j ∈ Finset.Ico 1 n,
      (1 / Real.sqrt (prefixSum q j)
        - 1 / Real.sqrt (prefixSum q (j + 1)))
      = 1 / Real.sqrt (prefixSum q 1) - 1 / Real.sqrt (prefixSum q n) :=
    telescope (fun j => 1 / Real.sqrt (prefixSum q j)) hn
  rw [← Finset.mul_sum, htel] at hbound
  have hPn : 0 ≤ 1 / Real.sqrt (prefixSum q n) := by
    have : 0 < prefixSum q n := prefix_pos n hn
    positivity
  have hP1 : 0 < Real.sqrt (prefixSum q 1) :=
    Real.sqrt_pos.mpr (prefix_pos 1 (le_refl 1))
  have hone : 2 * (1 / Real.sqrt (prefixSum q 1)
      - 1 / Real.sqrt (prefixSum q n)) ≤ 2 / Real.sqrt (prefixSum q 1) := by
    have : 2 * (1 / Real.sqrt (prefixSum q 1)
        - 1 / Real.sqrt (prefixSum q n))
        ≤ 2 * (1 / Real.sqrt (prefixSum q 1)) := by nlinarith [hPn]
    have he : 2 * (1 / Real.sqrt (prefixSum q 1))
        = 2 / Real.sqrt (prefixSum q 1) := by ring
    linarith [this, he]
  have hpq : prefixSum q 1 = popt q := by rw [prefixSum_one, popt]
  calc ∑ j ∈ Finset.Ico 1 n, searchTerm q j
      ≤ 2 * (1 / Real.sqrt (prefixSum q 1)
          - 1 / Real.sqrt (prefixSum q n)) := hbound
    _ ≤ 2 / Real.sqrt (prefixSum q 1) := hone
    _ = 2 / Real.sqrt (popt q) := by rw [hpq]

/-- For positive `C`, nonnegative `N` and weights, positive optimal mass, and `n ≥ 1`, the
weighted search sum multiplied by `2 * C * N` is at most `4 * C * N / sqrt (popt q)`. -/
theorem expected_queries_bound (q : ℕ → ℝ) (C N : ℝ) (hC : 0 < C) (hN : 0 ≤ N)
    (h0 : 0 < q 0) (hnn : ∀ i, 0 ≤ q i) (n : ℕ) (hn : 1 ≤ n) :
    2 * C * N * (∑ j ∈ Finset.Ico 1 n, searchTerm q j)
      ≤ 4 * C * N / Real.sqrt (popt q) := by
  have hsum := searchSum_bound q h0 hnn n hn
  have hfac : 0 ≤ 2 * C * N := by positivity
  have hmul : 2 * C * N * (∑ j ∈ Finset.Ico 1 n, searchTerm q j)
      ≤ 2 * C * N * (2 / Real.sqrt (popt q)) :=
    mul_le_mul_of_nonneg_left hsum hfac
  have he : 2 * C * N * (2 / Real.sqrt (popt q))
      = 4 * C * N / Real.sqrt (popt q) := by ring
  linarith [hmul, he.le, he.ge]

end Qatlib.Papers.QAOAScaling23.WeightedCost
