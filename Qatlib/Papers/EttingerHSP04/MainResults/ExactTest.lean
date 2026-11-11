/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact amplification and matrix correction bounds

The polynomial `ampProb` models one amplification step and separates probabilities `1 / 4` and
`3 / 4` exactly. Matrix correction estimates bound solutions of a perturbation recurrence and
place their coordinates in the unit interval under an explicit dimension bound. This develops
part of the framework of [EttingerHoyerKnill2004].

## Main statements

* `ampProb_quarter_three_quarters`: evaluates the amplification polynomial at the two
  distinguished probabilities.
* `lemma6_correction_bound`: bounds the coordinate correction by `3 / (4 * (r - 1))`.
* `lemma6_correction_unit`: places corrected coordinates in `[0, 1]` when `r ≥ 4`.

## References

* [Ettinger et al., 2004][EttingerHoyerKnill2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.EttingerHSP04.MainResults

open scoped BigOperators

/-- The amplification polynomial `p * (3 - 4 * p) ^ 2`. -/
noncomputable def ampProb (p : ℝ) : ℝ := p * (3 - 4 * p) ^ 2

/-- The real sine triple-angle identity. -/
theorem sin_three_mul_real (θ : ℝ) :
    Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by
  have h3 : (3 : ℝ) * θ = θ + 2 * θ := by ring
  rw [h3, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  have hs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  linear_combination (4 * Real.sin θ) * hs

/-- The amplification polynomial sends `sin θ ^ 2` to `sin (3 * θ) ^ 2`. See
[EttingerHoyerKnill2004]. -/
theorem ampProb_sin_sq (θ : ℝ) :
    ampProb (Real.sin θ ^ 2) = Real.sin (3 * θ) ^ 2 := by
  unfold ampProb
  rw [sin_three_mul_real]
  ring

/-- The amplification polynomial takes the value one at `1 / 4`. See [EttingerHoyerKnill2004]. -/
theorem ampProb_quarter : ampProb (1 / 4) = 1 := by
  unfold ampProb
  norm_num

/-- The amplification polynomial takes the value zero at `3 / 4`. See [EttingerHoyerKnill2004]. -/
theorem ampProb_three_quarters : ampProb (3 / 4) = 0 := by
  unfold ampProb
  norm_num

/-- The amplification polynomial sends `1 / 4` to one and `3 / 4` to zero. See
[EttingerHoyerKnill2004]. -/
theorem ampProb_quarter_three_quarters :
    ampProb (1 / 4) = 1 ∧ ampProb (3 / 4) = 0 :=
  ⟨ampProb_quarter, ampProb_three_quarters⟩

/-- If `p` is `1 / 4` or `3 / 4`, its amplified value is zero or one. -/
theorem ampProb_eq_zero_or_one {p : ℝ} (hp : p = 1 / 4 ∨ p = 3 / 4) :
    ampProb p = 0 ∨ ampProb p = 1 := by
  rcases hp with rfl | rfl
  · exact Or.inr ampProb_quarter
  · exact Or.inl ampProb_three_quarters

/-- The equation `(1 - Δ).mulVec x = y` yields the coordinate recurrence `x - y = Δ.mulVec x`.
See [EttingerHoyerKnill2004]. -/
theorem correction_recurrence {r : ℕ} (M Δ : Matrix (Fin r) (Fin r) ℝ)
    (hM : M = 1 - Δ) (x y : Fin r → ℝ) (hxy : M.mulVec x = y) :
    ∀ ν, x ν - y ν = ∑ μ, Δ ν μ * x μ := by
  intro ν
  have h := congrFun hxy ν
  rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec] at h
  simp only [Pi.sub_apply] at h
  have h2 : (Δ.mulVec x) ν = ∑ μ, Δ ν μ * x μ := rfl
  rw [h2] at h
  linarith

/-- For `r > 1`, entrywise bounds `|Δ i j| ≤ r⁻²` and the correction recurrence imply `|x ν - y
ν| ≤ 3 / (4 * (r - 1))` when each `y ν` is `1 / 4` or `3 / 4`. See [EttingerHoyerKnill2004]. -/
theorem lemma6_correction_bound {r : ℕ} (hr : 1 < r)
    (Δ : Matrix (Fin r) (Fin r) ℝ)
    (hΔ : ∀ i j, |Δ i j| ≤ ((r : ℝ)⁻¹) ^ 2)
    (x y : Fin r → ℝ) (hy : ∀ ν, y ν = 1/4 ∨ y ν = 3/4)
    (hx : ∀ ν, x ν - y ν = ∑ μ, Δ ν μ * x μ) (ν : Fin r) :
    |x ν - y ν| ≤ 3 / (4 * ((r : ℝ) - 1)) := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hr)
  have hrm1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    linarith
  have hSle : ∑ μ, |x μ| ≤ 3 * (r : ℝ) / 4 + ((r : ℝ)⁻¹) * ∑ μ, |x μ| := by
    calc ∑ ν, |x ν|
        ≤ ∑ ν, (3 / 4 + ∑ μ, |Δ ν μ| * |x μ|) := by
          apply Finset.sum_le_sum
          intro ν _
          have hyb : |y ν| ≤ 3 / 4 := by
            rcases hy ν with h | h <;> rw [h] <;> norm_num
          have hxeq : x ν = y ν + ∑ μ, Δ ν μ * x μ := by linarith [hx ν]
          calc |x ν| = |y ν + ∑ μ, Δ ν μ * x μ| := by rw [hxeq]
            _ ≤ |y ν| + |∑ μ, Δ ν μ * x μ| := abs_add_le _ _
            _ ≤ 3 / 4 + ∑ μ, |Δ ν μ| * |x μ| := by
                gcongr
                calc |∑ μ, Δ ν μ * x μ| ≤ ∑ μ, |Δ ν μ * x μ| :=
                      Finset.abs_sum_le_sum_abs _ _
                  _ = ∑ μ, |Δ ν μ| * |x μ| := by
                      apply Finset.sum_congr rfl
                      intro μ _
                      rw [abs_mul]
      _ = 3 / 4 * (r : ℝ) + ∑ ν, ∑ μ, |Δ ν μ| * |x μ| := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = 3 / 4 * (r : ℝ) + ∑ μ, (∑ ν, |Δ ν μ|) * |x μ| := by
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro μ _
          rw [← Finset.sum_mul]
      _ ≤ 3 / 4 * (r : ℝ) + ∑ μ, ((r : ℝ) * ((r : ℝ)⁻¹) ^ 2) * |x μ| := by
          gcongr with μ
          calc ∑ ν, |Δ ν μ| ≤ ∑ _ν : Fin r, ((r : ℝ)⁻¹) ^ 2 :=
                Finset.sum_le_sum (fun ν _ => hΔ ν μ)
            _ = (r : ℝ) * ((r : ℝ)⁻¹) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 3 * (r : ℝ) / 4 + ((r : ℝ)⁻¹) * ∑ μ, |x μ| := by
          have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
          have hcoef : (r : ℝ) * ((r : ℝ)⁻¹) ^ 2 = (r : ℝ)⁻¹ := by
            field_simp
          rw [hcoef, Finset.mul_sum]
          ring
  have hS_bound : ∑ μ, |x μ| ≤ 3 * (r : ℝ) ^ 2 / (4 * ((r : ℝ) - 1)) := by
    have hmul : (∑ μ, |x μ|) * (1 - (r : ℝ)⁻¹) ≤ 3 * (r : ℝ) / 4 := by
      nlinarith [hSle]
    have hpos : (0 : ℝ) < 1 - (r : ℝ)⁻¹ := by
      have : (r : ℝ)⁻¹ < 1 := by
        rw [inv_lt_one_iff₀]
        right
        exact_mod_cast hr
      linarith
    have hdiv : (∑ μ, |x μ|) ≤ (3 * (r : ℝ) / 4) / (1 - (r : ℝ)⁻¹) :=
      (le_div_iff₀ hpos).mpr hmul
    calc ∑ μ, |x μ| ≤ (3 * (r : ℝ) / 4) / (1 - (r : ℝ)⁻¹) := hdiv
      _ = 3 * (r : ℝ) ^ 2 / (4 * ((r : ℝ) - 1)) := by
          field_simp
  calc |x ν - y ν| = |∑ μ, Δ ν μ * x μ| := by rw [hx ν]
    _ ≤ ∑ μ, |Δ ν μ * x μ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ μ, |Δ ν μ| * |x μ| := by
        apply Finset.sum_congr rfl
        intro μ _
        rw [abs_mul]
    _ ≤ ∑ μ, ((r : ℝ)⁻¹) ^ 2 * |x μ| := by
        apply Finset.sum_le_sum
        intro μ _
        exact mul_le_mul_of_nonneg_right (hΔ ν μ) (abs_nonneg _)
    _ = ((r : ℝ)⁻¹) ^ 2 * ∑ μ, |x μ| := by rw [Finset.mul_sum]
    _ ≤ ((r : ℝ)⁻¹) ^ 2 * (3 * (r : ℝ) ^ 2 / (4 * ((r : ℝ) - 1))) := by
        exact mul_le_mul_of_nonneg_left hS_bound (sq_nonneg _)
    _ = 3 / (4 * ((r : ℝ) - 1)) := by
        have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
        field_simp

/-- For `r ≥ 4`, the stated entrywise bound and correction recurrence place every coordinate of
`x` in the unit interval. See [EttingerHoyerKnill2004]. -/
theorem lemma6_correction_unit {r : ℕ} (hr : 4 ≤ r)
    (Δ : Matrix (Fin r) (Fin r) ℝ)
    (hΔ : ∀ i j, |Δ i j| ≤ ((r : ℝ)⁻¹) ^ 2)
    (x y : Fin r → ℝ) (hy : ∀ ν, y ν = 1/4 ∨ y ν = 3/4)
    (hx : ∀ ν, x ν - y ν = ∑ μ, Δ ν μ * x μ) (ν : Fin r) :
    0 ≤ x ν ∧ x ν ≤ 1 := by
  classical
  have hbound := lemma6_correction_bound (by omega) Δ hΔ x y hy hx ν
  have hdelta : 3 / (4 * ((r : ℝ) - 1)) ≤ 1 / 4 := by
    have hrR : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hpos : (0 : ℝ) < 4 * ((r : ℝ) - 1) := by nlinarith
    rw [div_le_iff₀ hpos]
    nlinarith
  have hquarter : |x ν - y ν| ≤ 1 / 4 := le_trans hbound hdelta
  obtain ⟨hlo, hhi⟩ := abs_le.mp hquarter
  rcases hy ν with h | h
  · rw [h] at hlo hhi
    constructor <;> linarith
  · rw [h] at hlo hhi
    constructor <;> linarith

end Qatlib.Papers.EttingerHSP04.MainResults
