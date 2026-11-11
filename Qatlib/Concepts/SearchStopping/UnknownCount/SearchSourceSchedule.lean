/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule

/-!
# Parameterized capped exponential search schedules

Defines `SourceWidths` and `SourceSizes` for a general growth factor `l`. For `l ≥ 1`, the
schedule has a closed capped-power formula and positive ceiling sizes;
`search_source_schedule_instance` identifies the factor `6 / 5` specialization. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `search_source_schedule_laws`: For positive `N` and `l ≥ 1`, gives the capped-power width
  formula, positivity and exponential bounds for the ceiling sizes, and the equivalence between
  admissible indices and naturals below the width.
* `search_source_schedule_instance`: The fixed-factor schedules `ExponentialWidth` and
  `ExponentialSizes` equal the parameterized schedules at `l = 6 / 5`.
* `search_source_first_scale_crossing`: For `l > 1` and `m0 ≥ 1`, there is a positive exponent
  `K` with `m0 ≤ l ^ K ≤ l * m0`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.UnknownCount

/-- The search-width schedule starting at one and multiplying by `l` at each stage, capped at
`Real.sqrt N`. -/
noncomputable def SourceWidths (N : ℕ) (l : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => min (l * SourceWidths N l k) (Real.sqrt N)

/-- The natural-number ceiling of the parameterized width `SourceWidths N l k`. -/
noncomputable def SourceSizes (N : ℕ) (l : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (SourceWidths N l k)

/-- For positive `N` and `l ≥ 1`, gives the capped-power width formula, positivity and
exponential bounds for the ceiling sizes, and the equivalence between admissible indices and
naturals below the width. -/
theorem search_source_schedule_laws (N : ℕ) (hN : 0 < N) (l : ℝ) (hl : 1 ≤ l) :
    (∀ k, SourceWidths N l k = min (l ^ k) (Real.sqrt N)) ∧
    (∀ k, 0 < SourceSizes N l k) ∧
    (∀ k, (SourceSizes N l k : ℝ) ≤ 2 * l ^ k) ∧
    ∀ k j : ℕ, j < SourceSizes N l k ↔ (j : ℝ) < SourceWidths N l k := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcap : 1 ≤ Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hclosed (k : ℕ) : SourceWidths N l k = min (l ^ k) (Real.sqrt N) := by
    induction k with
    | zero => simp [SourceWidths, min_eq_left hcap]
    | succ k ih =>
      rw [SourceWidths, ih]
      by_cases hk : l ^ k ≤ Real.sqrt N
      · rw [min_eq_left hk, pow_succ]
        congr 1
        ring
      · have hc : Real.sqrt N ≤ l ^ k := le_of_not_ge hk
        have hc' : Real.sqrt N ≤ l * Real.sqrt N := by nlinarith
        have hk' : Real.sqrt N ≤ l ^ k * l :=
          hc.trans (le_mul_of_one_le_right (by positivity) hl)
        rw [min_eq_right hc, min_eq_right hc', pow_succ, min_eq_right hk']
  have hone (k : ℕ) : 1 ≤ l ^ k := one_le_pow₀ hl
  have hwidth (k : ℕ) : 0 < SourceWidths N l k := by
    rw [hclosed]
    exact lt_min (by positivity) (by linarith)
  refine ⟨hclosed, fun k => Nat.ceil_pos.mpr (hwidth k), ?_, fun _ _ => Nat.lt_ceil⟩
  intro k
  have hceil := Nat.ceil_lt_add_one (hwidth k).le
  have hw : SourceWidths N l k ≤ l ^ k := by rw [hclosed]; exact min_le_left _ _
  have ho := hone k
  change (Nat.ceil (SourceWidths N l k) : ℝ) ≤ _
  linarith

/-- The fixed-factor schedules `ExponentialWidth` and `ExponentialSizes` equal the parameterized
schedules at `l = 6 / 5`. -/
theorem search_source_schedule_instance (N : ℕ) :
    ExponentialWidth N = SourceWidths N (6 / 5) ∧
    ExponentialSizes N = SourceSizes N (6 / 5) := by
  have hw : ExponentialWidth N = SourceWidths N (6 / 5) := by
    funext k
    induction k with
    | zero => rfl
    | succ k ih => simp only [ExponentialWidth, SourceWidths, ih]
  exact ⟨hw, by funext k; simp only [ExponentialSizes, SourceSizes, hw]⟩

/-- For `l > 1` and `m0 ≥ 1`, there is a positive exponent `K` with `m0 ≤ l ^ K ≤ l * m0`. -/
theorem search_source_first_scale_crossing (l : ℝ) (hl : 1 < l)
    (m0 : ℝ) (hm0 : 1 ≤ m0) :
    ∃ K : ℕ, 0 < K ∧ m0 ≤ l ^ K ∧ l ^ K ≤ l * m0 := by
  obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near hm0 hl
  refine ⟨k + 1, by omega, hhi.le, ?_⟩
  rw [pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_left hlo (by linarith)

end Qatlib.Concepts.SearchStopping.UnknownCount
