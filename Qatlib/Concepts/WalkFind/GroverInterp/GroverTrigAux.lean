/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Trigonometric estimates for Grover interpolation

This module supplies explicit trigonometric bounds for the secular equation in the small-overlap
regime. The estimates control inverse spectral denominators, endpoint signs, iteration rounding,
and the final amplitude margin.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `grover_weighted_endpoint_signs`: bounds the secular expression at the two chosen endpoints.
* `grover_interpolation_iteration`: bounds the rounded quarter-turn iteration count.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.GroverInterp

/-- For `0 ≤ x ≤ 1`, the quantity `1 - cos x` lies between `x^2 / 3` and `x^2 / 2`. -/
theorem grover_one_sub_cos_bounds (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 / 3 ≤ 1 - Real.cos x ∧ 1 - Real.cos x ≤ x ^ 2 / 2 := by
  refine ⟨?_, by linarith [Real.one_sub_sq_div_two_le_cos (x := x)]⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hsin := Real.sin_gt_sub_cube (by linarith : 0 < x / 2)
  have hcube : x ^ 3 ≤ x := by
    have hsq : x ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsq)]
  have hs : 15 * x / 32 ≤ Real.sin (x / 2) := by nlinarith
  have hs0 : 0 ≤ Real.sin (x / 2) := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 15 * x / 32) hs
  have hid := Real.sin_sq_eq_half_sub (x / 2)
  have hxdouble : 2 * (x / 2) = x := by ring
  rw [hxdouble] at hid
  nlinarith

/-- For `0 ≤ β ≤ ε / 2` and `0 ≤ ε ≤ 1`, the cosine difference `cos β - cos ε` is at least `ε^2
/ 6`. -/
theorem grover_cos_separation (ε β : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hβ : 0 ≤ β) (hβhalf : β ≤ ε / 2) :
    ε ^ 2 / 6 ≤ Real.cos β - Real.cos ε := by
  have he := (grover_one_sub_cos_bounds ε hε hε1).1
  have hb := Real.one_sub_sq_div_two_le_cos (x := β)
  have hsq : β ^ 2 ≤ ε ^ 2 / 4 := by nlinarith
  nlinarith

/-- Nonnegative weights with eigenvalues in `[-1, cos ε]` give inverse-denominator sums between
half their total mass and `6 / ε^2` times that mass. -/
theorem grover_weighted_inverse_bounds {ι : Type*} [Fintype ι]
    (ε β : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβ : 0 ≤ β) (hβhalf : β ≤ ε / 2)
    (w eig : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (heig : ∀ j, -1 ≤ eig j ∧ eig j ≤ Real.cos ε) :
    (∑ j, w j) / 2 ≤ (∑ j, w j / (Real.cos β - eig j)) ∧
      (∑ j, w j / (Real.cos β - eig j)) ≤ 6 * (∑ j, w j) / ε ^ 2 := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hd (j : ι) : ε ^ 2 / 6 ≤ Real.cos β - eig j := by
    have hb := grover_cos_separation ε β hε.le hε1 hβ hβhalf
    linarith [(heig j).2]
  have hdp (j : ι) : 0 < Real.cos β - eig j := by
    linarith [hd j]
  have hdu (j : ι) : Real.cos β - eig j ≤ 2 := by
    linarith [Real.cos_le_one β, (heig j).1]
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_left (hw j) (hdp j) (hdu j)
  · have hpoint (j : ι) : w j / (Real.cos β - eig j) ≤ 6 * w j / ε ^ 2 := by
      have hs := div_le_div_of_nonneg_left (hw j)
        (by positivity : 0 < ε ^ 2 / 6) (hd j)
      convert! hs using 1
      ring
    calc
      _ ≤ ∑ j, 6 * w j / ε ^ 2 := Finset.sum_le_sum fun j _ => hpoint j
      _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]

/-- In the small-overlap regime, the weighted secular expression is nonpositive at `13 * α / 5`
and nonnegative at `ε * α / sqrt (2π)`. -/
theorem grover_weighted_endpoint_signs {ι : Type*} [Fintype ι]
    (ε α : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α)
    (hsmall : α ≤ ε ^ 2 / 200)
    (w eig : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hmass : (∑ j, w j) = 1 - α ^ 2)
    (heig : ∀ j, -1 ≤ eig j ∧ eig j ≤ Real.cos ε) :
    let lo := ε * α / Real.sqrt (2 * Real.pi)
    let hi := (13 / 5 : ℝ) * α
    α ^ 2 / (1 - Real.cos hi) - (∑ j, w j / (Real.cos hi - eig j)) ≤ 0 ∧
    0 ≤ α ^ 2 / (1 - Real.cos lo) - (∑ j, w j / (Real.cos lo - eig j)) := by
  let lo := ε * α / Real.sqrt (2 * Real.pi)
  let hi := (13 / 5 : ℝ) * α
  change α ^ 2 / (1 - Real.cos hi) - (∑ j, w j / (Real.cos hi - eig j)) ≤ 0 ∧
    0 ≤ α ^ 2 / (1 - Real.cos lo) - (∑ j, w j / (Real.cos lo - eig j))
  have he2 : ε ^ 2 ≤ ε := by nlinarith
  have ha1 : α ≤ 1 / 200 := by nlinarith
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hnn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  have hsp : 0 < Real.sqrt (2 * Real.pi) := by linarith
  have hlop : 0 < lo := by dsimp [lo]; positivity
  have hloa : lo ≤ ε * α := by
    dsimp [lo]
    exact div_le_self (by positivity) hs
  have hlohalf : lo ≤ ε / 2 := by nlinarith
  have hhip : 0 < hi := by dsimp [hi]; positivity
  have hhihalf : hi ≤ ε / 2 := by dsimp [hi]; nlinarith
  have hh1 : hi ≤ 1 := by linarith
  have hl1 : lo ≤ 1 := by linarith
  have hdhi : 0 < 1 - Real.cos hi := by
    have h := (grover_one_sub_cos_bounds hi hhip.le hh1).1
    nlinarith [sq_pos_of_pos hhip]
  have hdlo : 0 < 1 - Real.cos lo := by
    have h := (grover_one_sub_cos_bounds lo hlop.le hl1).1
    nlinarith [sq_pos_of_pos hlop]
  have hesq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hh := (grover_weighted_inverse_bounds ε hi hε hε1 hhip.le hhihalf w eig hw heig).1
  have hl := (grover_weighted_inverse_bounds ε lo hε hε1 hlop.le hlohalf w eig hw heig).2
  rw [hmass] at hh hl
  constructor
  · have hpole : α ^ 2 / (1 - Real.cos hi) ≤ 9 / 20 := by
      apply (div_le_iff₀ hdhi).mpr
      have hc := (grover_one_sub_cos_bounds hi hhip.le hh1).1
      dsimp [hi] at hc
      nlinarith [sq_nonneg α]
    have hm : (9 / 20 : ℝ) ≤ (1 - α ^ 2) / 2 := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr ha1)]
    linarith

  · have hlsq : (2 * Real.pi) * lo ^ 2 = ε ^ 2 * α ^ 2 := by
      dsimp [lo]
      rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      field_simp
    have hpole : 6 / ε ^ 2 ≤ α ^ 2 / (1 - Real.cos lo) := by
      apply (div_le_div_iff₀ hesq hdlo).mpr
      have hc := (grover_one_sub_cos_bounds lo hlop.le hl1).2
      nlinarith [mul_nonneg (sq_nonneg lo) (by linarith [Real.pi_gt_three] : 0 ≤ 2 * Real.pi - 3)]
    have hm : 6 * (1 - α ^ 2) / ε ^ 2 ≤ 6 / ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ hesq.le
      nlinarith [sq_nonneg α]
    linarith

/-- Rounding `π / (2β)` down gives at most `8 / (ε * α)` iterations and a remaining angle in
`[0, β)`. -/
theorem grover_interpolation_iteration (ε α β : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hβ : ε * α / Real.sqrt (2 * Real.pi) ≤ β) :
    let t := Nat.floor (Real.pi / (2 * β))
    (t : ℝ) ≤ 8 / (ε * α) ∧
      0 ≤ Real.pi / 2 - t * β ∧ Real.pi / 2 - t * β < β := by
  have hsp : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hβp : 0 < β := (by positivity : 0 < ε * α / Real.sqrt (2 * Real.pi)).trans_le hβ
  have ht := Nat.floor_le (by positivity : 0 ≤ Real.pi / (2 * β))
  have ht' := Nat.lt_floor_add_one (Real.pi / (2 * β))
  have hlo := (div_le_iff₀ hsp).mp hβ
  have hs3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hc : Real.pi * Real.sqrt (2 * Real.pi) ≤ 16 := by
    nlinarith [Real.pi_lt_four, Real.sqrt_nonneg (2 * Real.pi), Real.pi_pos]
  have hbudget : Real.pi / (2 * β) ≤ 8 / (ε * α) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * β) (by positivity : 0 < ε * α)).mpr
    have hmul := mul_le_mul_of_nonneg_left hlo Real.pi_pos.le
    have hhc := mul_le_mul_of_nonneg_right hc hβp.le
    nlinarith
  refine ⟨ht.trans hbudget, ?_, ?_⟩
  · have hh := (le_div_iff₀ (by positivity : 0 < 2 * β)).mp ht
    nlinarith
  · have hh := (div_lt_iff₀ (by positivity : 0 < 2 * β)).mp ht'
    nlinarith

/-- The weighted squared inverse-denominator sum is at most `6 / ε^2` times the corresponding
inverse-denominator sum. -/
theorem grover_weighted_inverse_square_bound {ι : Type*} [Fintype ι]
    (ε β : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β)
    (hβhalf : β ≤ ε / 2) (w eig : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (heig : ∀ j, -1 ≤ eig j ∧ eig j ≤ Real.cos ε) :
    (∑ j, w j / (Real.cos β - eig j) ^ 2) ≤
      (6 / ε ^ 2) * (∑ j, w j / (Real.cos β - eig j)) := by
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsep := grover_cos_separation ε β hε.le hε1 hβ hβhalf
  have hp : ∀ j, w j / (Real.cos β - eig j) ^ 2 ≤
      (6 / ε ^ 2) * (w j / (Real.cos β - eig j)) := by
    intro j
    have hd : ε ^ 2 / 6 ≤ Real.cos β - eig j := by linarith [(heig j).2]
    have hdp : 0 < Real.cos β - eig j := (by positivity : 0 < ε ^ 2 / 6).trans_le hd
    have hrec : 1 / (Real.cos β - eig j) ≤ 6 / ε ^ 2 := by
      apply (div_le_div_iff₀ hdp he2).mpr
      nlinarith
    have hn : 0 ≤ w j / (Real.cos β - eig j) := div_nonneg (hw j) hdp.le
    calc
      _ = (w j / (Real.cos β - eig j)) * (1 / (Real.cos β - eig j)) := by
        field_simp

      _ ≤ (w j / (Real.cos β - eig j)) * (6 / ε ^ 2) := mul_le_mul_of_nonneg_left hrec hn
      _ = _ := by ring
  calc
    _ ≤ ∑ j, (6 / ε ^ 2) * (w j / (Real.cos β - eig j)) := Finset.sum_le_sum fun j _ => hp j
    _ = _ := by rw [Finset.mul_sum]

/-- The small-overlap bounds leave an amplitude margin of at least `ε^3 / 1000` in the stated
error estimate. -/
theorem grover_small_overlap_amplitude_margin (ε α β : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsmall : α ≤ ε ^ 2 / 200)
    (hβ : β ≤ (13 / 5 : ℝ) * α) :
    ε ^ 3 / 1000 ≤ ε / 12 - (4 * β / ε + β) := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε := by
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
  have hb2 : β ≤ 13 * ε ^ 2 / 1000 := by nlinarith
  have hb1 : β ≤ 13 * ε / 1000 := by nlinarith
  have hd : 4 * β / ε ≤ 52 * ε / 1000 := by
    apply (div_le_iff₀ hε).mpr
    nlinarith
  nlinarith

end Qatlib.Concepts.WalkFind.GroverInterp
