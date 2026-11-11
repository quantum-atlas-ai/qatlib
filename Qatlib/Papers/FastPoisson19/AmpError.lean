/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Amplitude-error bounds for reciprocal rotation

This module bounds the reciprocal error from a one-sided eigenvalue estimate and the difference
between a reciprocal and the implemented reciprocal-square-root amplitude. Their combination
gives a maximum-based total-error bound, together with a concrete counterexample to the printed
difference-based expression. These statements concern the formulas and models in [WangEtAl2020].

## Main statements

* `source_total_amplitude_error`: bounds the actual amplitude error by the maximum of two powers
  of one half.
* `total_error_main_limit`: simplifies that maximum for `f ≥ 4`.
* `printed_display_counterexample`: proves the printed expression is too small at the stated
  parameters.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.AmpError

/-- For an underestimate `lamhat ≥ 8` with error below `2^(-f)`, the reciprocal error is
nonnegative and strictly below `2^(-(f + 6))`. -/
theorem phase_estimation_reciprocal_error (f : ℕ) {lam lamhat : ℝ}
    (h8 : 8 ≤ lamhat) (hle : lamhat ≤ lam) (hdelta : lam - lamhat < (1 / 2 : ℝ) ^ f) :
    0 ≤ 1 / lamhat - 1 / lam ∧ 1 / lamhat - 1 / lam < (1 / 2 : ℝ) ^ (f + 6) := by
  have hlamhat : 0 < lamhat := by linarith
  have hlam : 0 < lam := lt_of_lt_of_le hlamhat hle
  have hden : 0 < lamhat * lam := mul_pos hlamhat hlam
  have hrewrite : 1 / lamhat - 1 / lam = (lam - lamhat) / (lamhat * lam) := by
    field_simp
  have hnonneg : 0 ≤ 1 / lamhat - 1 / lam := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hlamhat hle
  have hlt : 1 / lamhat - 1 / lam < (1 / 2 : ℝ) ^ (f + 6) := by
    rw [hrewrite]
    have h1 : (lam - lamhat) / (lamhat * lam) < (1 / 2 : ℝ) ^ f / (lamhat * lam) :=
      div_lt_div_of_pos_right hdelta hden
    have h2 : (1 / 2 : ℝ) ^ f / (lamhat * lam) ≤ (1 / 2 : ℝ) ^ f / (lamhat ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [hlamhat, hle])
    have h3 : (1 / 2 : ℝ) ^ f / (lamhat ^ 2) ≤ (1 / 2 : ℝ) ^ f / 64 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith [h8])
    have h4 : (1 / 2 : ℝ) ^ f / 64 = (1 / 2 : ℝ) ^ (f + 6) := by
      rw [pow_add]
      norm_num
      ring
    linarith
  exact ⟨hnonneg, hlt⟩

/-- For `x ≥ 8`, the difference `1 / sqrt (1 + x^2) - 1 / x` lies strictly between `-2^(-10)`
and zero. -/
theorem sqrt_reciprocal_sub_reciprocal_bounds (x : ℝ) (hx : 8 ≤ x) :
    -(1 / 2 : ℝ) ^ 10 < 1 / Real.sqrt (1 + x ^ 2) - 1 / x ∧
      1 / Real.sqrt (1 + x ^ 2) - 1 / x < 0 := by
  have hx0 : 0 < x := by linarith
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsx : x < Real.sqrt (1 + x ^ 2) := by
    rw [Real.lt_sqrt (le_of_lt hx0)]
    linarith [sq_nonneg x]
  constructor
  · have hdiff : 1 / x - 1 / Real.sqrt (1 + x ^ 2) < 1 / (2 * x ^ 3) := by
      have hden : Real.sqrt (1 + x ^ 2) + x ≠ 0 := by positivity
      have hmul : (Real.sqrt (1 + x ^ 2) - x) * (Real.sqrt (1 + x ^ 2) + x) = 1 := by
        nlinarith [hsq]
      have hnum : Real.sqrt (1 + x ^ 2) - x = 1 / (Real.sqrt (1 + x ^ 2) + x) := by
        field_simp
        linarith [hmul]
      have hrw : 1 / x - 1 / Real.sqrt (1 + x ^ 2) =
          (Real.sqrt (1 + x ^ 2) - x) / (x * Real.sqrt (1 + x ^ 2)) := by
        field_simp
      rw [hrw, hnum, div_div]
      have h2x : (0 : ℝ) < 2 * x ^ 3 := by positivity
      have hBA : 2 * x ^ 3 <
          (Real.sqrt (1 + x ^ 2) + x) * (x * Real.sqrt (1 + x ^ 2)) := by
        have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
        have hxs : x * x ^ 2 < Real.sqrt (1 + x ^ 2) * x ^ 2 :=
          mul_lt_mul_of_pos_right hsx hx2pos
        have hexp : (Real.sqrt (1 + x ^ 2) + x) * (x * Real.sqrt (1 + x ^ 2)) =
            x * Real.sqrt (1 + x ^ 2) ^ 2 + x ^ 2 * Real.sqrt (1 + x ^ 2) := by ring
        rw [hexp, hsq]
        nlinarith [hxs, hx0]
      exact one_div_lt_one_div_of_lt h2x hBA
    have h512 : (512 : ℝ) ≤ x ^ 3 := by
      have h8 : (8 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
      norm_num at h8
      exact h8
    have hle10 : 1 / (2 * x ^ 3) ≤ (1 / 2 : ℝ) ^ 10 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 / 2 : ℝ) ^ 10 * (2 * x ^ 3) = x ^ 3 / 512 := by norm_num; ring
      rw [this]
      linarith
    have hneg : 1 / Real.sqrt (1 + x ^ 2) - 1 / x =
        -(1 / x - 1 / Real.sqrt (1 + x ^ 2)) := by ring
    rw [hneg]
    have hlt : 1 / x - 1 / Real.sqrt (1 + x ^ 2) < (1 / 2 : ℝ) ^ 10 :=
      lt_of_lt_of_le hdiff hle10
    linarith
  · exact sub_neg.mpr (one_div_lt_one_div_of_lt hx0 hsx)

/-- Under the one-sided phase-estimation error assumptions, the absolute amplitude error is less
than the maximum of `2^(-(f + 6))` and `2^(-10)`. This bounds the implemented amplitude
expression from [WangEtAl2020]. -/
theorem source_total_amplitude_error (f : ℕ) {lam lamhat : ℝ}
    (h8 : 8 ≤ lamhat) (hle : lamhat ≤ lam) (hdelta : lam - lamhat < (1 / 2 : ℝ) ^ f) :
    |1 / Real.sqrt (1 + lamhat ^ 2) - 1 / lam| <
      max ((1 / 2 : ℝ) ^ (f + 6)) ((1 / 2 : ℝ) ^ 10) := by
  have h1 := phase_estimation_reciprocal_error f h8 hle hdelta
  have h2 := sqrt_reciprocal_sub_reciprocal_bounds lamhat h8
  have key : 1 / Real.sqrt (1 + lamhat ^ 2) - 1 / lam =
      (1 / Real.sqrt (1 + lamhat ^ 2) - 1 / lamhat) + (1 / lamhat - 1 / lam) := by
    ring
  rw [key, abs_lt]
  constructor
  · have hlt : -(1 / 2 : ℝ) ^ 10 <
        (1 / Real.sqrt (1 + lamhat ^ 2) - 1 / lamhat) + (1 / lamhat - 1 / lam) := by
      linarith [h1.1, h2.1]
    exact lt_of_le_of_lt (neg_le_neg (le_max_right ((1 / 2 : ℝ) ^ (f + 6)) ((1 / 2 : ℝ) ^ 10))) hlt
  · have hlt : (1 / Real.sqrt (1 + lamhat ^ 2) - 1 / lamhat) + (1 / lamhat - 1 / lam) <
        (1 / 2 : ℝ) ^ (f + 6) := by
      linarith [h1.2, h2.2]
    exact lt_of_lt_of_le hlt (le_max_left ((1 / 2 : ℝ) ^ (f + 6)) ((1 / 2 : ℝ) ^ 10))

/-- The absolute difference of the two displayed error scales is at most their maximum. -/
theorem paper_total_error_display_le_max (f : ℕ) :
    |(1 / 2 : ℝ) ^ (f + 6) - (1 / 2 : ℝ) ^ 10| ≤
      max ((1 / 2 : ℝ) ^ (f + 6)) ((1 / 2 : ℝ) ^ 10) := by
  have ha : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (f + 6) := by positivity
  have hb : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 10 := by norm_num
  rcases le_total ((1 / 2 : ℝ) ^ 10) ((1 / 2 : ℝ) ^ (f + 6)) with h | h
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]
    linarith

/-- For `f ≥ 4`, the maximum of the two error scales is `2^(-10)`. -/
theorem total_error_main_limit (f : ℕ) (hf : 4 ≤ f) :
    max ((1 / 2 : ℝ) ^ (f + 6)) ((1 / 2 : ℝ) ^ 10) = (1 / 2 : ℝ) ^ 10 := by
  apply max_eq_right
  have h : (1 / 2 : ℝ) ^ 10 ≥ (1 / 2 : ℝ) ^ (f + 6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact h

/-- At eigenvalue eight and `f = 4`, the actual amplitude error is strictly greater than the
printed difference-based error expression from [WangEtAl2020]. -/
theorem printed_display_counterexample :
    |1 / Real.sqrt (1 + (8 : ℝ) ^ 2) - 1 / 8| >
      |(1 / 2 : ℝ) ^ (4 + 6 : ℕ) - (1 / 2 : ℝ) ^ 10| := by
  have hn := (sqrt_reciprocal_sub_reciprocal_bounds 8 (by norm_num)).2
  have hp : 0 < |1 / Real.sqrt (1 + (8 : ℝ) ^ 2) - 1 / 8| := abs_pos.mpr (ne_of_lt hn)
  norm_num only [show (4 + 6 : ℕ) = 10 by norm_num, sub_self, abs_zero]
  norm_num at hp
  exact abs_pos.mpr (by simpa only [one_div] using hp)

end Qatlib.Papers.FastPoisson19.AmpError
