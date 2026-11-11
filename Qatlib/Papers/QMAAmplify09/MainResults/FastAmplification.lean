/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAAmplify09.MainResults.Defs
import Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phase separation and fast QMA amplification

This module proves the acceptance-to-phase gap estimate and explicit real-valued resource bounds
for the fast QMA amplification analysis of [NagajWocjanZhang2009]. The reciprocal phase gap
controls `phaseEstimationDepth`, while `amplificationCost` combines the constant-confidence cost
with repeated estimates.

The final result `theorem1_fast_amplification` packages the resource bound with the binomial
failure and complementary acceptance bounds; it is an inequality statement about these
quantities.

## Main statements

* `phaseGap_ge`: lower bound on phase separation in terms of the acceptance gap.
* `phaseEstimationCost_le`: constant-confidence phase-estimation cost bound.
* `theorem1_fast_amplification`: combined cost, failure, and acceptance estimates.

## References

* [Nagaj et al., 2009][NagajWocjanZhang2009]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.QMAAmplify09.MainResults.Defs
open Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma

namespace Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification

/-- For `0 ≤ y ≤ x ≤ 1`, the difference of inverse sines is at least `x - y`. -/
theorem arcsin_sub_ge {x y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : x ≤ 1) :
    x - y ≤ Real.arcsin x - Real.arcsin y := by
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hy1 : y ≤ 1 := le_trans hyx hx1
  rcases eq_or_lt_of_le hyx with hxy | hlt
  · rw [← hxy]
    simp
  have hxpos : 0 < x := lt_of_le_of_lt hy0 hlt
  have hsum : 0 < x + y := by linarith
  have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h1y : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hsqx : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1x
  have hsqy : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt h1y

  set D := x * Real.sqrt (1 - y ^ 2) - y * Real.sqrt (1 - x ^ 2) with hDdef
  have hsiny : Real.sin (Real.arcsin y) = y := Real.sin_arcsin (by linarith) hy1
  have hsinx : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hsin : Real.sin (Real.arcsin x - Real.arcsin y) = D := by
    rw [Real.sin_sub, hsinx, hsiny, Real.cos_arcsin, Real.cos_arcsin, hDdef]
    ring
  have hdpi : Real.arcsin x - Real.arcsin y ≤ Real.pi / 2 := by
    have h1 := Real.arcsin_le_pi_div_two x
    have h2 : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr hy0
    linarith

  have hsle : Real.sqrt (1 - x ^ 2) ≤ Real.sqrt (1 - y ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := by
    have h1 : y * Real.sqrt (1 - x ^ 2) ≤ x * Real.sqrt (1 - x ^ 2) :=
      mul_le_mul_of_nonneg_right hyx hs2
    have h2 : x * Real.sqrt (1 - x ^ 2) ≤ x * Real.sqrt (1 - y ^ 2) :=
      mul_le_mul_of_nonneg_left hsle hx0
    rw [hDdef]
    linarith

  have hDsum : D * (x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2)) = x ^ 2 - y ^ 2 := by
    rw [hDdef]
    nlinarith [hsqx, hsqy]
  have hsum_le : x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2) ≤ x + y := by
    have h1 : Real.sqrt (1 - y ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg y])
    have h2 : Real.sqrt (1 - x ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
    have hs1 : 0 ≤ Real.sqrt (1 - y ^ 2) := Real.sqrt_nonneg _
    have hs2' : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hxyprod : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
  have hDge : x - y ≤ D := by
    have h1 : D * (x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2)) ≤ D * (x + y) :=
      mul_le_mul_of_nonneg_left hsum_le hD0
    have h2 : x ^ 2 - y ^ 2 ≤ D * (x + y) := by linarith [h1, hDsum]
    have h3 : (x - y) * (x + y) ≤ D * (x + y) := by
      rw [hxyprod]
      exact h2
    exact le_of_mul_le_mul_right h3 hsum

  have hD1 : D ≤ 1 := by
    have h1 : Real.sqrt (1 - y ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg y])
    have h2 : 0 ≤ y * Real.sqrt (1 - x ^ 2) :=
      mul_nonneg hy0 (Real.sqrt_nonneg _)
    have h3 : x * Real.sqrt (1 - y ^ 2) ≤ x := by
      simpa using mul_le_mul_of_nonneg_left h1 hx0
    rw [hDdef]
    linarith
  have hd0 : 0 ≤ Real.arcsin x - Real.arcsin y :=
    sub_nonneg.mpr (Real.arcsin_le_arcsin hyx)
  have hd_eq : Real.arcsin D = Real.arcsin x - Real.arcsin y := by
    rw [← hsin]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) hdpi
  have hsinD : Real.sin D ≤ D := by
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h]
      simp
    · exact le_of_lt (Real.sin_lt h)
  have hle : D ≤ Real.arcsin D := by
    have hmem : D ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.one_le_pi_div_two]
    have hmem2 : D ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hD1⟩
    exact (Real.le_arcsin_iff_sin_le hmem hmem2).mpr hsinD
  linarith

/-- For nonnegative `b < a`, rationalizing the difference of square roots gives `(a - b) / (√a +
√b)`. -/
theorem sqrt_sub_eq_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : b < a) :
    Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (lt_of_le_of_lt hb h)
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs : 0 < Real.sqrt a + Real.sqrt b := by linarith
  rw [eq_div_iff hs.ne']
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [h1, h2]

/-- The phase gap of promise bounds is at least `(a - b) / (π * (√a + √b))`. See
[NagajWocjanZhang2009]. -/
theorem phaseGap_ge (P : PromiseBounds) :
    (P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b)) ≤ P.phaseGap := by
  have hx1 : Real.sqrt P.a ≤ 1 := Real.sqrt_le_one.mpr P.a_le_one
  have hyx : Real.sqrt P.b ≤ Real.sqrt P.a := Real.sqrt_le_sqrt P.lt.le
  have harc : Real.sqrt P.a - Real.sqrt P.b ≤
      Real.arcsin (Real.sqrt P.a) - Real.arcsin (Real.sqrt P.b) :=
    arcsin_sub_ge (Real.sqrt_nonneg P.b) hyx hx1
  have hphase : P.phaseGap =
      (Real.arcsin (Real.sqrt P.a) - Real.arcsin (Real.sqrt P.b)) / Real.pi := by
    unfold PromiseBounds.phaseGap phaseOfProbability blockAngle
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
    ring
  rw [hphase]
  have hsqrt_gap : Real.sqrt P.a - Real.sqrt P.b =
      (P.a - P.b) / (Real.sqrt P.a + Real.sqrt P.b) :=
    sqrt_sub_eq_div P.a_nonneg P.b_nonneg P.lt
  have hrewrite : (P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b)) =
      (Real.sqrt P.a - Real.sqrt P.b) / Real.pi := by
    rw [hsqrt_gap]
    field_simp
  rw [hrewrite]
  exact div_le_div_of_nonneg_right harc Real.pi_pos.le

/-- The phase gap of any `PromiseBounds` is strictly positive. -/
theorem phaseGap_pos (P : PromiseBounds) : 0 < P.phaseGap := by
  have h := phaseGap_ge P
  have hpos : 0 < (P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b)) := by
    apply div_pos P.gap_pos
    have hsa : 0 < Real.sqrt P.a := Real.sqrt_pos.2 P.a_pos
    have hsb : 0 ≤ Real.sqrt P.b := Real.sqrt_nonneg P.b
    exact mul_pos Real.pi_pos (by linarith)
  linarith

/-- The real-valued phase-estimation depth parameter, defined as the reciprocal of the phase
gap. -/
noncomputable def phaseEstimationDepth (P : PromiseBounds) : ℝ := 1 / P.phaseGap

/-- The phase-estimation depth is at most `π * (√a + √b) / (a - b)`. See [NagajWocjanZhang2009]. -/
theorem phaseEstimationDepth_le (P : PromiseBounds) :
    phaseEstimationDepth P ≤ Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b) := by
  have hg := phaseGap_ge P
  have hcpos : 0 < (P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b)) := by
    apply div_pos P.gap_pos
    have hsa : 0 < Real.sqrt P.a := Real.sqrt_pos.2 P.a_pos
    have hsb : 0 ≤ Real.sqrt P.b := Real.sqrt_nonneg P.b
    exact mul_pos Real.pi_pos (by linarith)
  have h1 : phaseEstimationDepth P ≤
      1 / ((P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b))) := by
    unfold phaseEstimationDepth
    exact one_div_le_one_div_of_le hcpos hg
  have h2 : 1 / ((P.a - P.b) / (Real.pi * (Real.sqrt P.a + Real.sqrt P.b))) =
      Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b) := by
    field_simp
  linarith [h1, h2.le, h2.ge]

/-- The real-valued phase-estimation cost `(2 + 1 / (2 * ε)) * phaseEstimationDepth P - 1`. -/
noncomputable def phaseEstimationCost (P : PromiseBounds) (ε : ℝ) : ℝ :=
  (2 + 1 / (2 * ε)) * phaseEstimationDepth P - 1

/-- At error parameter `1 / 16`, the phase-estimation cost is at most `10 * π * (√a + √b) / (a -
b)`. See [NagajWocjanZhang2009]. -/
theorem phaseEstimationCost_le (P : PromiseBounds) :
    phaseEstimationCost P (1 / 16) ≤
      10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b) := by
  have hfac : (2 + 1 / (2 * ((1 : ℝ) / 16))) = 10 := by norm_num
  have hd := phaseEstimationDepth_le P
  have hd0 : 0 ≤ phaseEstimationDepth P := by
    unfold phaseEstimationDepth
    exact div_nonneg zero_le_one (phaseGap_pos P).le
  have h1 : phaseEstimationCost P (1 / 16) ≤ 10 * phaseEstimationDepth P := by
    unfold phaseEstimationCost
    rw [hfac]
    linarith
  have h2 : 10 * phaseEstimationDepth P ≤
      10 * (Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b)) :=
    mul_le_mul_of_nonneg_left hd (by norm_num)
  have h3 : 10 * (Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b)) =
      10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b) := by
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- The cost of `r` repetitions of phase estimation with error parameter `1 / 16`. -/
noncomputable def amplificationCost (P : PromiseBounds) (r : ℕ) : ℝ :=
  (r : ℝ) * phaseEstimationCost P (1 / 16)

/-- The amplification cost is at most `10 * π * (√a + √b) * r / (a - b)`. -/
theorem amplificationCost_le (P : PromiseBounds) (r : ℕ) :
    amplificationCost P r ≤
      10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (r : ℝ) / (P.a - P.b) := by
  have hc := phaseEstimationCost_le P
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h1 : amplificationCost P r ≤
      (r : ℝ) * (10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b)) := by
    unfold amplificationCost
    exact mul_le_mul_of_nonneg_left hc hr
  have h2 : (r : ℝ) * (10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) / (P.a - P.b)) =
      10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (r : ℝ) / (P.a - P.b) := by
    ring
  linarith [h1, h2.le, h2.ge]

/-- The strict-majority bad mass at error parameter `1 / 16` is at most `2 ^ (-r)`. See
[NagajWocjanZhang2009]. -/
theorem theorem1_yes_failure (r : ℕ) :
    badMass (1 / 16) r ≤ (2 : ℝ) ^ (-(r : ℤ)) :=
  le_trans (median_failure_bound (by norm_num) (by norm_num) r)
    (median_failure_bound_eps16 r)

/-- The complement of the bad mass at error parameter `1 / 16` is at least `1 - 2 ^ (-r)`. See
[NagajWocjanZhang2009]. -/
theorem theorem1_yes_acceptance (r : ℕ) :
    1 - (2 : ℝ) ^ (-(r : ℤ)) ≤ 1 - badMass (1 / 16) r := by
  linarith [theorem1_yes_failure r]

/-- The amplification cost bound and the complementary failure and acceptance bounds hold
simultaneously. See [NagajWocjanZhang2009]. -/
theorem theorem1_fast_amplification (P : PromiseBounds) (r : ℕ) :
    amplificationCost P r ≤
        10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (r : ℝ) / (P.a - P.b) ∧
      badMass (1 / 16) r ≤ (2 : ℝ) ^ (-(r : ℤ)) ∧
      1 - (2 : ℝ) ^ (-(r : ℤ)) ≤ 1 - badMass (1 / 16) r :=
  ⟨amplificationCost_le P r, theorem1_yes_failure r, theorem1_yes_acceptance r⟩

end Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification
