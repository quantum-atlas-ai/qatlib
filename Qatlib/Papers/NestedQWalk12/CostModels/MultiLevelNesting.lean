/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Closed form of a multilevel cost recurrence

This module defines the scalar nested-walk recurrence `mcTail` and its prefix-product expansion
`mcClosed`, following the cost expression in Corollary 4.1 of [JefferyKothariMagniez2013].
`ampFactor` and `gapFactor` are reciprocal square-root factors, and `pref` multiplies
amplification factors over consecutive levels.

`mcTail_eq_closed` proves that the recursive and expanded expressions agree. Adding the setup
cost gives `corollary41`, with a separate nonnegativity theorem under positive level parameters
and nonnegative costs.

## Main statements

* `mcTail_eq_closed`: the cost recurrence equals its finite-sum expansion.
* `corollary41`: setup plus weighted update costs and the weighted final checking cost.
* `corollary41_nonneg`: the total modeled cost is nonnegative under the stated assumptions.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option autoImplicit false
noncomputable section

open scoped Real BigOperators

namespace Qatlib.Papers.NestedQWalk12.CostModels.MultiLevelNesting

/-- The reciprocal square root of the marked-fraction parameter at level n. -/
def ampFactor (ε : ℕ → ℝ) (n : ℕ) : ℝ := 1 / Real.sqrt (ε n)

/-- The reciprocal square root of the spectral-gap parameter at level n. -/
def gapFactor (δ : ℕ → ℝ) (n : ℕ) : ℝ := 1 / Real.sqrt (δ n)

/-- The product of `ampFactor` over m consecutive levels starting at n. -/
def pref (ε : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, ampFactor ε (n + j)

/-- The scalar cost recurrence for m nested levels starting at n, with terminal checking cost C
and update cost U at each level. -/
def mcTail (C : ℝ) (ε δ U : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _n, 0 => C
  | n, m + 1 => ampFactor ε n * (gapFactor δ n * U n + mcTail C ε δ U (n + 1) m)

/-- The finite-sum cost expression with each update term weighted by its amplification prefix
and gap factor, and terminal cost C weighted by the full prefix. -/
def mcClosed (C : ℝ) (ε δ U : ℕ → ℝ) (n m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, pref ε n (i + 1) * gapFactor δ (n + i) * U (n + i))
    + pref ε n m * C

/-- The amplification prefix over zero levels equals one. -/
lemma pref_zero (ε : ℕ → ℝ) (n : ℕ) : pref ε n 0 = 1 := by
  simp [pref]

/-- Extending an amplification prefix by one level multiplies it by `ampFactor` at level n + m. -/
lemma pref_succ (ε : ℕ → ℝ) (n m : ℕ) :
    pref ε n (m + 1) = pref ε n m * ampFactor ε (n + m) := by
  simp [pref, Finset.prod_range_succ]

/-- A nonempty amplification prefix factors as its first level's amplification factor times the
prefix starting at the next level. -/
lemma pref_shift (ε : ℕ → ℝ) (n i : ℕ) :
    pref ε n (i + 1) = ampFactor ε n * pref ε (n + 1) i := by
  simp only [pref]
  rw [Finset.prod_range_succ']
  have h : (∏ j ∈ Finset.range i, ampFactor ε (n + (j + 1)))
      = ∏ j ∈ Finset.range i, ampFactor ε ((n + 1) + j) := by
    apply Finset.prod_congr rfl
    intro j _
    rw [show n + (j + 1) = (n + 1) + j by ring]
  rw [h]
  exact mul_comm _ _

/-- The closed cost expression for m + 1 levels satisfies the same one-step nesting recurrence
as `mcTail`. -/
lemma mcClosed_succ (C : ℝ) (ε δ U : ℕ → ℝ) (n m : ℕ) :
    mcClosed C ε δ U n (m + 1) =
      ampFactor ε n * (gapFactor δ n * U n + mcClosed C ε δ U (n + 1) m) := by
  unfold mcClosed
  rw [Finset.sum_range_succ']
  have hA : (∑ i ∈ Finset.range m,
        pref ε n (i + 1 + 1) * gapFactor δ (n + (i + 1)) * U (n + (i + 1)))
      = ampFactor ε n * ∑ i ∈ Finset.range m,
          pref ε (n + 1) (i + 1) * gapFactor δ ((n + 1) + i) * U ((n + 1) + i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pref_shift ε n (i + 1), show n + (i + 1) = (n + 1) + i by ring]
    ring
  rw [hA]
  simp only [Nat.zero_add, Nat.add_zero]
  rw [pref_shift ε n m, show pref ε n 1 = ampFactor ε n from by simp [pref]]
  ring

/-- The recursive scalar cost `mcTail` equals its prefix-product expansion `mcClosed` for every
starting level and depth. -/
lemma mcTail_eq_closed (C : ℝ) (ε δ U : ℕ → ℝ) (n m : ℕ) :
    mcTail C ε δ U n m = mcClosed C ε δ U n m := by
  induction m generalizing n with
  | zero => simp [mcTail, mcClosed, pref_zero]
  | succ m ih =>
      simp only [mcTail]
      rw [ih (n + 1), ← mcClosed_succ]

/-- The total scalar multilevel cost, consisting of setup cost S plus the depth-k recurrence
starting at level zero. -/
def mcCost (S C : ℝ) (ε δ U : ℕ → ℝ) (k : ℕ) : ℝ :=
  S + mcTail C ε δ U 0 k

/-- The total scalar multilevel cost equals setup plus the prefix-weighted sum of update costs
and the full-prefix-weighted checking cost. This is the recurrence identity associated with
[Jeffery et al., Corollary 4.1][JefferyKothariMagniez2013]. -/
theorem corollary41 (S C : ℝ) (ε δ U : ℕ → ℝ) (k : ℕ) :
    mcCost S C ε δ U k =
      S + (∑ i ∈ Finset.range k,
              pref ε 0 (i + 1) * gapFactor δ i * U i)
            + pref ε 0 k * C := by
  unfold mcCost
  rw [mcTail_eq_closed]
  unfold mcClosed
  simp only [Nat.zero_add]
  ring

/-- With positive marked-fraction and spectral-gap parameters and nonnegative setup, checking,
and update costs, `mcCost` is nonnegative. -/
theorem corollary41_nonneg (S C : ℝ) (ε δ U : ℕ → ℝ) (k : ℕ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (_hε : ∀ i, 0 < ε i) (_hδ : ∀ i, 0 < δ i) (hU : ∀ i, 0 ≤ U i) :
    0 ≤ mcCost S C ε δ U k := by
  have hpref : ∀ n j, 0 ≤ pref ε n j := by
    intro n j
    refine Finset.prod_nonneg ?_
    intro i _
    unfold ampFactor
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hgap : ∀ i, 0 ≤ gapFactor δ i := by
    intro i
    unfold gapFactor
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  rw [corollary41]
  have hsum : 0 ≤ ∑ i ∈ Finset.range k, pref ε 0 (i + 1) * gapFactor δ i * U i := by
    refine Finset.sum_nonneg ?_
    intro i _
    exact mul_nonneg (mul_nonneg (hpref 0 (i + 1)) (hgap i)) (hU i)
  have := mul_nonneg (hpref 0 k) hC
  linarith

end Qatlib.Papers.NestedQWalk12.CostModels.MultiLevelNesting
