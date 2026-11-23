/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearnGraphDis12.MainResults.StageMath7
import Mathlib.Algebra.Order.Floor.Semiring

public section

/-!
# Integer stage size for graph collision

[Belovs2012], §4.2 of the [fixed preprint](https://arxiv.org/abs/1205.1534v2).
Round half the continuous optimizer upward. For at least four vertices this
keeps two positions available for the collision certificate and preserves the
order of the two terms in the paper's stage-cost estimate, with a uniform
constant. The estimate is arithmetic and assumes the two stage-cost terms;
the counting routine and the learning-graph construction are separate.
-/

namespace Qatlib.Papers.LearnGraphDis12.MainResults

/-- An integer setup size leaves room for two certificate positions and bounds
the two-term stage cost by `4 √n α^(1/6)`, uniformly in the graph size and
independence number. -/
theorem exists_integer_stage_size (n α : ℕ) (hn : 4 ≤ n) (hα : 1 ≤ α) (hαn : α ≤ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r + 2 ≤ n ∧
      (r : ℝ) * Real.sqrt ((α : ℝ) / n) + n / Real.sqrt r ≤
        4 * Real.sqrt n * (α : ℝ) ^ (1 / 6 : ℝ) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hα' : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hαn' : (α : ℝ) ≤ n := by exact_mod_cast hαn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hα₀ : (0 : ℝ) < α := by linarith
  let t : ℝ := (n : ℝ) * (α : ℝ) ^ (-(1 / 3 : ℝ))
  have ht₁ : 1 ≤ t := by
    have ha : (α : ℝ) ^ (1 / 3 : ℝ) ≤ n :=
      (Real.rpow_le_self_of_one_le hα' (by norm_num)).trans hαn'
    dsimp [t]
    rw [Real.rpow_neg hα₀.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hα₀ _),
      one_mul]
    exact ha
  have htn : t ≤ n := by
    have ha : (α : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hα' (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
    exact mul_le_of_le_one_right hn₀.le ha
  let r := ⌈t / 2⌉₊
  have htpos : 0 < t / 2 := by linarith
  have hr : 1 ≤ r := Nat.one_le_ceil_iff.mpr htpos
  have hrn : r ≤ n - 2 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    linarith
  refine ⟨r, hr, by omega, ?_⟩
  have hlo : t / 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hhi : (r : ℝ) ≤ 2 * t := by
    have h := Nat.ceil_lt_add_one htpos.le
    change (r : ℝ) < t / 2 + 1 at h
    linarith
  have hrs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hts : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_four : Real.sqrt 4 = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
    norm_num
  have hs : Real.sqrt t ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      _ ≤ Real.sqrt (4 * (r : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt_four]
  have hsetup : (r : ℝ) * Real.sqrt ((α : ℝ) / n) ≤
      2 * (t * Real.sqrt ((α : ℝ) / n)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hhi (Real.sqrt_nonneg _)
  have hlast : (n : ℝ) / Real.sqrt r ≤ 2 * ((n : ℝ) / Real.sqrt t) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hrs hts).mpr
    rw [mul_comm 2 (n : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left hs hn₀.le
  have hopt := Qatlib.Papers.LearnGraphDis12.MainResults.learningGraph_complexity_optimized
    n α hn₀ hα₀
  change t * Real.sqrt ((α : ℝ) / n) + n / Real.sqrt t = _ at hopt
  calc
    _ ≤ 2 * (t * Real.sqrt ((α : ℝ) / n) + n / Real.sqrt t) := by linarith
    _ = _ := by rw [hopt]; ring

end Qatlib.Papers.LearnGraphDis12.MainResults
