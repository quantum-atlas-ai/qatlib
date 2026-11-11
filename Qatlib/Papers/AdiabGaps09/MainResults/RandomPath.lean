/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabGaps09.MainResults.CubeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Random paths and second-order energy crossings

Defines the scalar second-order energy branches `energyL` and `energyU` and proves that a
negative curvature difference prevents their crossing on the open interpolation interval.
Counting estimates for positive `secondOrderGap` values give a uniform positive fraction of
favorable bit strings and a finite repetition bound. See [FarhiEtAl2011].

## Main statements

* `random_path_removes_crossing`: A negative coefficient difference excludes equality of the two
  energy branches.
* `substantial_probability_positive`: Eventually a fixed positive fraction of bit strings has
  positive second-order gap.
* `constant_retries_exists`: A fixed positive success probability reaches probability at least
  one half after finitely many repetitions.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators
open Qatlib.Papers.AdiabGaps09.MainResults

namespace Qatlib.Papers.AdiabGaps09.MainResults.RandomPath

/-- The lower scalar energy branch with second-order coefficient `e2`, equal to `(1 - s) * (n /
2) + s * (((1 - s) / s) ^ 2 * e2)`. -/
def energyL (n e2 s : ℝ) : ℝ :=
  (1 - s) * (n / 2) + s * (((1 - s) / s) ^ 2 * e2)

/-- The upper scalar energy branch, including an additional offset `s / 2` relative to the
corresponding lower branch. -/
def energyU (n e2 s : ℝ) : ℝ :=
  (1 - s) * (n / 2) + s * ((1 / 2) + ((1 - s) / s) ^ 2 * e2)

/-- The difference of the two energy branches factors as `s` times the sum of the offset `-1 /
2` and the scaled coefficient difference. -/
theorem energy_diff (n eL eU s : ℝ) :
    energyL n eL s - energyU n eU s
      = s * (-(1 / 2) + ((1 - s) / s) ^ 2 * (eL - eU)) := by
  unfold energyL energyU
  ring

/-- The negative of `secondOrderGap d z`, representing the coefficient difference for the chosen
bit string. -/
def randomGapDiff {k : ℕ} (d : Fin k → ℝ) (z : Fin k → Bool) : ℝ :=
  -(secondOrderGap d z)

/-- A positive second-order gap gives a negative `randomGapDiff`. -/
theorem randomGapDiff_neg {k : ℕ} (d : Fin k → ℝ) (z : Fin k → Bool)
    (h : 0 < secondOrderGap d z) : randomGapDiff d z < 0 := by
  unfold randomGapDiff
  linarith

/-- If `eL - eU < 0`, the lower energy branch lies strictly below the upper branch for every `0
< s < 1` [FarhiEtAl2011]. -/
theorem no_crossing_of_negative_gap (n eL eU : ℝ) (hD : eL - eU < 0) :
    ∀ s : ℝ, 0 < s → s < 1 → energyL n eL s < energyU n eU s := by
  intro s hs0 _
  have hsq : 0 ≤ ((1 - s) / s) ^ 2 := sq_nonneg _
  have hprod : ((1 - s) / s) ^ 2 * (eL - eU) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsq (le_of_lt hD)
  have hsum : -(1 / 2) + ((1 - s) / s) ^ 2 * (eL - eU) < 0 := by linarith
  have hneg : s * (-(1 / 2) + ((1 - s) / s) ^ 2 * (eL - eU)) < 0 :=
    mul_neg_of_pos_of_neg hs0 hsum
  have hdiff : energyL n eL s - energyU n eU s < 0 := by
    rw [energy_diff]
    exact hneg
  linarith

/-- A negative coefficient difference excludes a crossing of the two scalar energy branches in
`0 < s < 1` [FarhiEtAl2011]. -/
theorem random_path_removes_crossing (n eL eU : ℝ) (hD : eL - eU < 0) :
    ¬ ∃ s : ℝ, 0 < s ∧ s < 1 ∧ energyL n eL s = energyU n eU s := by
  rintro ⟨s, hs0, hs1, heq⟩
  have hlt := no_crossing_of_negative_gap n eL eU hD s hs0 hs1
  linarith

/-- If the sums of the coefficient arrays are eventually positive, a fixed positive fraction of
all bit strings eventually has positive second-order gap [FarhiEtAl2011]. -/
theorem substantial_probability_positive (d : (n : ℕ) → Fin n → ℝ)
    (h : ∀ᶠ n in Filter.atTop, 0 < ∑ i, d n i) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in Filter.atTop,
      p * (2 : ℝ) ^ n
        ≤ ((Finset.univ.filter
              (fun z : Fin n → Bool => 0 < secondOrderGap (d n) z)).card : ℝ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [h] with n hn
  have hbase := card_ge_half_of_mean (d n)
  have hsub : (Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d n i ≤ secondOrderGap (d n) z))
      ⊆ (Finset.univ.filter (fun z : Fin n → Bool =>
        0 < secondOrderGap (d n) z)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    nlinarith [hn]
  have hcast : ((Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d n i ≤ secondOrderGap (d n) z)).card : ℝ)
      ≤ ((Finset.univ.filter (fun z : Fin n → Bool =>
        0 < secondOrderGap (d n) z)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc (1 / 2) * (2 : ℝ) ^ n = (2 : ℝ) ^ n / 2 := by ring
    _ ≤ _ := hbase
    _ ≤ _ := hcast

/-- For `0 < p ≤ 1`, some positive natural number `K` satisfies `1 / 2 ≤ 1 - (1 - p) ^ K`
[FarhiEtAl2011]. -/
theorem constant_retries_exists (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ 1 / 2 ≤ 1 - (1 - p) ^ K := by
  have hb : 1 - p < 1 := by linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hb
  refine ⟨K, ?_, by linarith⟩
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h
    simp only [pow_zero] at hK
    exact absurd hK (by norm_num)
  · exact h

end Qatlib.Papers.AdiabGaps09.MainResults.RandomPath
