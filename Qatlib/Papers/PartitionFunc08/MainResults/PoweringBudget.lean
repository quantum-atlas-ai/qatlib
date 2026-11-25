/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PartitionFunc08.MainResults.Powering

@[expose] public section

/-!
# Repetition budget for median powering

Lemma 2 reduces failure by taking the median of an odd number of independent
outputs. The exponential tail gives a sufficient integer repetition budget.
-/

set_option autoImplicit false

namespace Qatlib.Papers.PartitionFunc08.MainResults

/-- The logarithmic budget makes the failure bound of the powering lemma at most `δ`. -/
theorem tail_le (k : ℕ) {p δ : ℝ} (hp : 1 / 2 < p) (hδ : 0 < δ)
    (hbudget : Real.log (1 / δ) ≤ 2 * (2 * (k : ℝ) + 1) * (p - 1 / 2) ^ 2) :
    Real.exp (-(2 * (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) /
      (2 * (k : ℝ) + 1)) ≤ δ := by
  let n : ℝ := 2 * (k : ℝ) + 1
  let x : ℝ := n * (p - 1 / 2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hx : 0 < x := mul_pos hn (sub_pos.mpr hp)
  have heq : (k : ℝ) + 1 - n * (1 - p) = x + 1 / 2 := by
    dsimp [n, x]
    ring
  have hsq : x ^ 2 ≤ (x + 1 / 2) ^ 2 :=
    (sq_le_sq₀ hx.le (by positivity)).2 (by linarith)
  have hmul : 2 * n * (p - 1 / 2) ^ 2 = 2 * x ^ 2 / n := by
    dsimp [x]
    field_simp [hn.ne']
  have hlog : Real.log (1 / δ) ≤ 2 * x ^ 2 / n := hbudget.trans_eq hmul
  have hbound := hlog.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hn.le)
  apply (Real.le_log_iff_exp_le hδ).mp
  rw [one_div, Real.log_inv] at hbound
  change -(2 * (((k : ℝ) + 1) - n * (1 - p)) ^ 2) / n ≤ Real.log δ
  rw [heq, neg_div]
  linarith

/-- An odd number of trials bounded by the inverse squared gap times the log of inverse failure
plus three suffices for the powering tail. -/
theorem budget_exists {p δ : ℝ} (hp : 1 / 2 < p) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ k : ℕ,
      (2 * (k : ℝ) + 1) < Real.log (1 / δ) / (2 * (p - 1 / 2) ^ 2) + 3 ∧
      Real.exp (-(2 * (((k : ℝ) + 1) - (2 * (k : ℝ) + 1) * (1 - p)) ^ 2) /
        (2 * (k : ℝ) + 1)) ≤ δ := by
  let x := Real.log (1 / δ) / (4 * (p - 1 / 2) ^ 2)
  let k := ⌈x⌉₊
  have hden : 0 < 4 * (p - 1 / 2) ^ 2 := by positivity
  have hx : 0 ≤ x := div_nonneg (Real.log_nonneg ((le_div_iff₀ hδ).2 (by simpa using hδ₁))) hden.le
  have hlo : x ≤ (k : ℝ) := Nat.le_ceil _
  have hhi : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have heq : 2 * x = Real.log (1 / δ) / (2 * (p - 1 / 2) ^ 2) := by
    dsimp [x]
    field_simp [ne_of_gt (sub_pos.mpr hp)]
    ring
  refine ⟨k, ?_, tail_le k hp hδ ?_⟩
  · linarith
  · have hmul := (div_le_iff₀ hden).mp hlo
    nlinarith [sq_nonneg (p - 1 / 2)]

end Qatlib.Papers.PartitionFunc08.MainResults
