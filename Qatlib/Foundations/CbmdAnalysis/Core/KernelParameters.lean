/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelTail
import Qatlib.Foundations.CbmdAnalysis.Core.KernelAuxiliary

/-!
# Choosing integer-kernel approximation parameters

`kernelOrder`, `kernelCutoff`, and `kernelSpacing` choose sampling parameters from the tolerance
and growth budget. Their bounds separately control the real-sample tail and the auxiliary
correction, and ensure compatibility with the contour growth estimates.

The module records the exact number of retained indices and explicit bounds on their frequencies
and total count. These estimates quantify the finite sampling construction in [WangEtAl2026].

## Main statements

* `integerWeight_chosen_tail_le`: bounds the discarded weight mass.
* `integerAuxiliary_chosen_le`: bounds the auxiliary correction at the chosen spacing.
* `kernelLCU_card_log_bound`: gives an explicit logarithmic sample-count estimate.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

/-- The tail constant `5 * integerWeightConstant * exp 2`. -/
noncomputable def kernelTailConstant : ℝ := 5 * integerWeightConstant * Real.exp 2

/-- The universal integer weight constant is strictly positive. -/
theorem integerWeightConstant_pos : 0 < integerWeightConstant := by
  have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
  simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
  unfold integerWeightConstant
  exact mul_pos (by positivity) (lt_of_lt_of_le (by norm_num) h)

/-- The kernel tail constant is strictly positive. -/
theorem kernelTailConstant_pos : 0 < kernelTailConstant := by
  unfold kernelTailConstant
  exact mul_pos (mul_pos (by norm_num) integerWeightConstant_pos) (Real.exp_pos _)

/-- One plus the natural-number ceiling of `max 0 (log (kernelTailConstant / δ) / 2)`. -/
noncomputable def kernelOrder (δ : ℝ) : ℕ :=
  1 + ⌈max 0 (Real.log (kernelTailConstant / δ) / 2)⌉₊

/-- The natural-number ceiling of `2 * a * kernelOrder δ`, used as the symmetric sampling
cutoff. -/
noncomputable def kernelCutoff (a δ : ℝ) : ℕ := ⌈2 * a * kernelOrder δ⌉₊

/-- The chosen kernel order is at least one. -/
theorem kernelOrder_pos (δ : ℝ) : 1 ≤ kernelOrder δ := by
  unfold kernelOrder
  omega

/-- The chosen order is at least `log (kernelTailConstant / δ) / 2` and less than its
nonnegative part plus two. -/
theorem kernelOrder_bounds (δ : ℝ) :
    Real.log (kernelTailConstant / δ) / 2 ≤ (kernelOrder δ : ℝ) ∧
    (kernelOrder δ : ℝ) < max 0 (Real.log (kernelTailConstant / δ) / 2) + 2 := by
  have hl := Nat.le_ceil (max 0 (Real.log (kernelTailConstant / δ) / 2))
  have hu := Nat.ceil_lt_add_one (le_max_left 0 (Real.log (kernelTailConstant / δ) / 2))
  unfold kernelOrder
  push_cast
  constructor
  · linarith [le_max_right 0 (Real.log (kernelTailConstant / δ) / 2)]
  · linarith

/-- For positive tolerance, the exponential tail estimate at the chosen order is at most `δ`. -/
theorem kernelOrder_tail_budget {δ : ℝ} (hδ : 0 < δ) :
    kernelTailConstant * Real.exp (-2 * (kernelOrder δ : ℝ)) ≤ δ := by
  have hC := kernelTailConstant_pos
  have hl := (kernelOrder_bounds δ).1
  have he : -2 * (kernelOrder δ : ℝ) ≤ Real.log (δ / kernelTailConstant) := by
    rw [Real.log_div hδ.ne' hC.ne']
    rw [Real.log_div hC.ne' hδ.ne'] at hl
    linarith
  have h := Real.exp_le_exp.mpr he
  rw [Real.exp_log (div_pos hδ hC)] at h
  have hm := mul_le_mul_of_nonneg_left h hC.le
  convert! hm using 1
  field_simp

/-- For positive tolerance and `a ≥ 1`, the total norm of the weights beyond the chosen cutoff
is at most `δ`. -/
theorem integerWeight_chosen_tail_le {δ a : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a) :
    (∑' k : {k : ℤ // (kernelCutoff a δ : ℤ) < |k|},
      ‖integerWeight (kernelOrder δ) a ((k.val : ℝ) / a)‖) ≤ δ := by
  have ht := integerWeight_tail_tsum_le (kernelOrder δ) (kernelOrder_pos δ) ha
    (kernelCutoff a δ) (Nat.le_ceil _)
  exact ht.trans (kernelOrder_tail_budget hδ)

/-- The symmetric integer interval determined by the chosen cutoff contains exactly `2 *
kernelCutoff a δ + 1` indices. -/
theorem kernelCutoff_card (a δ : ℝ) :
    (Finset.Icc (-(kernelCutoff a δ : ℤ)) (kernelCutoff a δ)).card =
      2 * kernelCutoff a δ + 1 := by
  rw [Int.card_Icc]
  omega

/-- For `a ≥ 1`, the chosen cutoff divided by `a` is less than `2 * kernelOrder δ + 1`. -/
theorem kernelCutoff_frequency_lt {a : ℝ} (ha : 1 ≤ a) (δ : ℝ) :
    (kernelCutoff a δ : ℝ) / a < 2 * (kernelOrder δ : ℝ) + 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hk := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * a * (kernelOrder δ : ℝ) by positivity)
  unfold kernelCutoff
  apply (div_lt_iff₀ ha0).mpr
  nlinarith

/-- For `a ≥ 1`, each retained frequency has absolute value less than `2 * max 0 (log
(kernelTailConstant / δ) / 2) + 5`. -/
theorem kernelRetained_frequency_lt {a : ℝ} (ha : 1 ≤ a) (δ : ℝ) (k : ℤ)
    (hk : k ∈ Finset.Icc (-(kernelCutoff a δ : ℤ)) (kernelCutoff a δ)) :
    |(k : ℝ) / a| < 2 * max 0 (Real.log (kernelTailConstant / δ) / 2) + 5 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hk' := Finset.mem_Icc.mp hk
  have habs : |(k : ℝ)| ≤ kernelCutoff a δ := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hk'.1
    · exact_mod_cast hk'.2
  have hr : |(k : ℝ) / a| ≤ (kernelCutoff a δ : ℝ) / a := by
    rw [abs_div, abs_of_pos ha0]
    exact div_le_div_of_nonneg_right habs ha0.le
  have hfreq := kernelCutoff_frequency_lt ha δ
  have hm := (kernelOrder_bounds δ).2
  linarith

/-- For `a ≥ 1`, the retained index count is less than `4a * (max 0 (log (kernelTailConstant /
δ) / 2) + 2) + 3`. -/
theorem kernelCutoff_card_lt {a : ℝ} (ha : 1 ≤ a) (δ : ℝ) :
    ((Finset.Icc (-(kernelCutoff a δ : ℤ)) (kernelCutoff a δ)).card : ℝ) <
      4 * a * (max 0 (Real.log (kernelTailConstant / δ) / 2) + 2) + 3 := by
  rw [kernelCutoff_card]
  push_cast
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hk := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * a * (kernelOrder δ : ℝ) by positivity)
  have hm := (kernelOrder_bounds δ).2
  unfold kernelCutoff
  nlinarith

/-- The maximum of one and `(ρ + log (kernelAuxiliaryConstant * (m + 1) / δ)) / (2π)`, chosen to
control auxiliary residues. -/
noncomputable def kernelSpacing (ρ δ : ℝ) (m : ℕ) : ℝ :=
  max 1 ((ρ + Real.log (kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ)) / (2 * Real.pi))

/-- The chosen spacing parameter is at least one. -/
theorem kernelSpacing_ge_one (ρ δ : ℝ) (m : ℕ) : 1 ≤ kernelSpacing ρ δ m := le_max_left _ _

/-- For positive tolerance, the chosen spacing makes `ρ - 2πa` at most `log (δ /
(kernelAuxiliaryConstant * (m + 1)))`. -/
theorem kernelSpacing_gap (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ρ - 2 * Real.pi * kernelSpacing ρ δ m ≤
      Real.log (δ / (kernelAuxiliaryConstant * ((m : ℝ) + 1))) := by
  have hC : 0 < kernelAuxiliaryConstant * ((m : ℝ) + 1) := by
    have h := kernelAuxiliaryConstant_ge_twelve
    positivity
  have hmax := le_max_right 1
    ((ρ + Real.log (kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ)) / (2 * Real.pi))
  have hm := (div_le_iff₀ (show 0 < 2 * Real.pi by positivity)).mp hmax
  have hlog : Real.log (δ / (kernelAuxiliaryConstant * ((m : ℝ) + 1))) =
      -Real.log (kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ) := by
    rw [Real.log_div hδ.ne' hC.ne', Real.log_div hC.ne' hδ.ne']
    ring
  rw [hlog]
  unfold kernelSpacing
  linarith only [hm]

/-- For `0 < δ ≤ 1`, the chosen spacing satisfies the growth condition `ρ ≤ 2πa`. -/
theorem kernelSpacing_growth_le (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ) :
    ρ ≤ 2 * Real.pi * kernelSpacing ρ δ m := by
  have hC : 1 ≤ kernelAuxiliaryConstant * ((m : ℝ) + 1) := by
    have h := kernelAuxiliaryConstant_ge_twelve
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hratio : 1 ≤ kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hlog := Real.log_nonneg hratio
  have hmax := le_max_right 1
    ((ρ + Real.log (kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ)) / (2 * Real.pi))
  have hm := (div_le_iff₀ (show 0 < 2 * Real.pi by positivity)).mp hmax
  unfold kernelSpacing
  linarith

/-- For `0 < δ ≤ 1` and the stated auxiliary growth bounds, the correction at `kernelSpacing ρ δ
m` has norm at most `δ`. -/
theorem integerAuxiliary_chosen_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (m : ℕ) (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (U : ℂ → E)
    (hUtop : ‖U (2 * Complex.I)‖ ≤ Real.exp (2 * ρ))
    (hUrow : ∀ r ∈ Finset.Icc (-(m : ℤ)) m, ‖U ((r : ℂ) + Complex.I)‖ ≤ Real.exp ρ) :
    ‖integerAuxiliaryCorrection m (kernelSpacing ρ δ m) U‖ ≤ δ := by
  have hC : 0 < kernelAuxiliaryConstant * ((m : ℝ) + 1) := by
    have h := kernelAuxiliaryConstant_ge_twelve
    positivity
  have ha : 0 < kernelSpacing ρ δ m :=
    lt_of_lt_of_le (by norm_num) (kernelSpacing_ge_one _ _ _)
  have haux := integerAuxiliary_norm_le m ha (kernelSpacing_growth_le ρ hδ hδ1 m) U hUtop hUrow
  have hexp := Real.exp_le_exp.mpr (kernelSpacing_gap ρ hδ m)
  rw [Real.exp_log (div_pos hδ hC)] at hexp
  have hmul := mul_le_mul_of_nonneg_left hexp hC.le
  have hbudget : kernelAuxiliaryConstant * ((m : ℝ) + 1) *
      Real.exp (ρ - 2 * Real.pi * kernelSpacing ρ δ m) ≤ δ := by
    convert! hmul using 1
    have hC0 : kernelAuxiliaryConstant ≠ 0 := by
      have h := kernelAuxiliaryConstant_ge_twelve
      linarith
    field_simp [hC0]
  exact haux.trans hbudget

/-- For nonnegative growth budget and `0 < δ ≤ 1`, the chosen spacing is at most `1 + (ρ + log
(kernelAuxiliaryConstant / δ) + m) / (2π)`. -/
theorem kernelSpacing_le (ρ : ℝ) (hρ : 0 ≤ ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (m : ℕ) :
    kernelSpacing ρ δ m ≤
      1 + (ρ + Real.log (kernelAuxiliaryConstant / δ) + m) / (2 * Real.pi) := by
  have hC : 0 < kernelAuxiliaryConstant := by
    have h := kernelAuxiliaryConstant_ge_twelve
    linarith
  have hratio : 1 ≤ kernelAuxiliaryConstant / δ := by
    apply (le_div_iff₀ hδ).mpr
    have h := kernelAuxiliaryConstant_ge_twelve
    linarith
  have hlog := Real.log_nonneg hratio
  have hm := Real.log_le_sub_one_of_pos (show 0 < (m : ℝ) + 1 by positivity)
  have hsplit : Real.log (kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ) =
      Real.log (kernelAuxiliaryConstant / δ) + Real.log ((m : ℝ) + 1) := by
    rw [show kernelAuxiliaryConstant * ((m : ℝ) + 1) / δ =
      (kernelAuxiliaryConstant / δ) * ((m : ℝ) + 1) by ring]
    exact Real.log_mul (div_ne_zero hC.ne' hδ.ne') (by positivity)
  unfold kernelSpacing
  apply max_le_iff.mpr
  constructor
  · have hnonneg : 0 ≤ (ρ + Real.log (kernelAuxiliaryConstant / δ) + m) / (2 * Real.pi) :=
      div_nonneg (by positivity) (by positivity)
    linarith
  · rw [hsplit, ← add_assoc]
    have hdiv := div_le_div_of_nonneg_right
      (show ρ + Real.log (kernelAuxiliaryConstant / δ) + Real.log ((m : ℝ) + 1) ≤
        ρ + Real.log (kernelAuxiliaryConstant / δ) + m by linarith)
      (show 0 ≤ 2 * Real.pi by positivity)
    linarith

/-- For nonnegative growth budget and `0 < δ ≤ 1`, the prescribed half-tolerance parameters give
the stated explicit bound on the retained index count in terms of `ρ` and logarithms of the
tolerance. -/
theorem kernelLCU_card_log_bound (ρ : ℝ) (hρ : 0 ≤ ρ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let B := max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 2
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    ((Finset.Icc (-(kernelCutoff a (δ / 2) : ℤ)) (kernelCutoff a (δ / 2))).card : ℝ) <
      4 * (1 + (ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B) / (2 * Real.pi)) * B + 3 := by
  (try dsimp only)
  let B := max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 2
  let m := kernelOrder (δ / 2)
  let a := kernelSpacing ρ (δ / 2) m
  have hm : (m : ℝ) < B := (kernelOrder_bounds _).2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha := kernelSpacing_le ρ hρ (show 0 < δ / 2 by positivity) (by linarith : δ / 2 ≤ 1) m
  have hadiv := div_le_div_of_nonneg_right
    (show ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + m ≤
      ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B by linarith)
    (show 0 ≤ 2 * Real.pi by positivity)
  have ha' : a ≤ 1 + (ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B) / (2 * Real.pi) := by
    exact ha.trans (by linarith)
  have hcard := kernelCutoff_card_lt (kernelSpacing_ge_one ρ (δ / 2) m) (δ / 2)
  change _ < 4 * a * B + 3 at hcard
  change _ < 4 *
      (1 + (ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B) / (2 * Real.pi)) * B + 3
  exact hcard.trans_le (by nlinarith [mul_le_mul_of_nonneg_right ha' hB])

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
