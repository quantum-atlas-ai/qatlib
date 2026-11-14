/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Numerical probability and register bounds

These real inequalities supply explicit powers-of-two bounds for the success expressions in the
regulator and principal-ideal models. Further logarithmic inequalities convert size constraints
on q and form parameters into register-size bounds [Schmidt2009].

## Main statements

* `dual_count_bound`: A bounded range of run lengths gives the regulator counting constant.
* `pip_dual_count_bound`: The corresponding principal-ideal counting expression has a fixed
  lower bound.
* `first_register_bits_bound`: A size bound for q gives a base-two logarithmic register bound.

## References

* [Schmidt, 2009][Schmidt2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrincIdeal09.MainResults

/-- The constant `6 / π²` is strictly greater than one half [Schmidt2009]. -/
theorem six_div_pi_sq_gt_half : (1 / 2 : ℝ) < 6 / Real.pi ^ 2 := by
  have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsq : Real.pi ^ 2 < 12 := by nlinarith [hpi_lt, hpi_pos]
  have hpos : 0 < Real.pi ^ 2 := by positivity
  rw [lt_div_iff₀ hpos]
  nlinarith [hsq]

/-- The quantity `(6 / π²) * 2^(-25)` is at least `2^(-26)` [Schmidt2009]. -/
theorem thm2_prob_bound : (2 : ℝ) ^ (-26 : ℤ) ≤ (6 / Real.pi ^ 2) * (2 : ℝ) ^ (-25 : ℤ) := by
  have h := six_div_pi_sq_gt_half
  have h2 : (2 : ℝ) ^ (-25 : ℤ) = 2 * (2 : ℝ) ^ (-26 : ℤ) := by
    rw [show (-25 : ℤ) = -26 + 1 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_one]; ring
  rw [h2]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-26 : ℤ) := by positivity
  nlinarith [h, hpos]

/-- The quantity `(6 / π²) * 2^(-35)` is at least `2^(-37)` [Schmidt2009]. -/
theorem thm4_prob_bound : (2 : ℝ) ^ (-37 : ℤ) ≤ (6 / Real.pi ^ 2) * (2 : ℝ) ^ (-35 : ℤ) := by
  have h := six_div_pi_sq_gt_half
  have h2 : (2 : ℝ) ^ (-35 : ℤ) = 4 * (2 : ℝ) ^ (-37 : ℤ) := by
    rw [show (-35 : ℤ) = -37 + 2 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_two]; ring
  rw [h2]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-37 : ℤ) := by positivity
  nlinarith [h, hpos]

/-- If `mmin ≥ 1` and `mmax ≤ mmin + 4`, then `(mmin + 1) / (2^9 * (mmax + 1)) ≥ 2^(-11)`
[Schmidt2009]. -/
theorem dual_count_bound {mmin mmax : ℕ} (hmin : 1 ≤ mmin) (hmax : mmax ≤ mmin + 4) :
    (2 : ℝ) ^ (-11 : ℤ) ≤
      ((mmin : ℝ) + 1) / (2 ^ 9 * ((mmax : ℝ) + 1)) := by
  have hminR : (1 : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmin
  have hmaxR : (mmax : ℝ) ≤ (mmin : ℝ) + 4 := by exact_mod_cast hmax
  have hkey : (mmax : ℝ) + 1 ≤ 4 * ((mmin : ℝ) + 1) := by nlinarith
  have h211 : (2 : ℝ) ^ (-11 : ℤ) = 1 / 2048 := by norm_num
  rw [h211]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 9 * ((mmax : ℝ) + 1))]
  have heq : (1 / 2048 : ℝ) * (2 ^ 9 * ((mmax : ℝ) + 1)) = ((mmax : ℝ) + 1) / 4 := by
    norm_num
    ring
  rw [heq]
  linarith

/-- If `mmin ≥ 1` and `mmax ≤ mmin + 4`, then `(mmin + 1) / (2^13 * (mmax + 2)) ≥ 2^(-16)`
[Schmidt2009]. -/
theorem pip_dual_count_bound {mmin mmax : ℕ} (hmin : 1 ≤ mmin) (hmax : mmax ≤ mmin + 4) :
    (2 : ℝ) ^ (-16 : ℤ) ≤
      ((mmin : ℝ) + 1) / (2 ^ 13 * ((mmax : ℝ) + 2)) := by
  have hminR : (1 : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmin
  have hmaxR : (mmax : ℝ) ≤ (mmin : ℝ) + 4 := by exact_mod_cast hmax
  have hkey : (mmax : ℝ) + 2 ≤ 8 * ((mmin : ℝ) + 1) := by nlinarith
  have h216 : (2 : ℝ) ^ (-16 : ℤ) = 1 / 65536 := by norm_num
  rw [h216]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 13 * ((mmax : ℝ) + 2))]
  have heq : (1 / 65536 : ℝ) * (2 ^ 13 * ((mmax : ℝ) + 2)) = ((mmax : ℝ) + 2) / 8 := by
    norm_num
    ring
  rw [heq]
  linarith

/-- The base-two logarithm of ten is at most five. -/
theorem logb_two_ten_le_five : Real.logb 2 10 ≤ 5 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 10)]
  norm_num

/-- If `Δ > 1` and `0 < q ≤ 10 * Δ * (log Δ)²`, then `logb 2 q ≤ logb 2 Δ + 2 * logb 2 (log Δ) +
5`. -/
theorem first_register_bits_bound {Δ q : ℝ} (hΔ : 1 < Δ) (hq : 0 < q)
    (hq_le : q ≤ 10 * Δ * (Real.log Δ) ^ 2) :
    Real.logb 2 q ≤ Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) + 5 := by
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hlogpos : (0 : ℝ) < Real.log Δ := Real.log_pos hΔ
  have hpos : (0 : ℝ) < 10 * Δ * (Real.log Δ) ^ 2 := by positivity
  have hmono : Real.logb 2 q ≤ Real.logb 2 (10 * Δ * (Real.log Δ) ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hq hq_le
  have hmul : Real.logb 2 (10 * Δ * (Real.log Δ) ^ 2)
      = Real.logb 2 10 + Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) := by
    rw [Real.logb_mul (by positivity : (10 : ℝ) * Δ ≠ 0)
          (by positivity : (Real.log Δ) ^ 2 ≠ 0),
        Real.logb_mul (by norm_num : (10 : ℝ) ≠ 0) (by linarith : Δ ≠ 0)]
    rw [Real.logb_pow]
    ring
  calc Real.logb 2 q ≤ Real.logb 2 (10 * Δ * (Real.log Δ) ^ 2) := hmono
    _ = Real.logb 2 10 + Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) := hmul
    _ ≤ Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) + 5 := by
        have := logb_two_ten_le_five; linarith

/-- If `Δ > 1` and `0 < q ≤ Δ * (log Δ)² / 2`, then `logb 2 q ≤ logb 2 Δ + 2 * logb 2 (log Δ)`
[Schmidt2009]. -/
theorem pip_register_bits_bound {Δ q : ℝ} (hΔ : 1 < Δ) (hq : 0 < q)
    (hq_le : q ≤ Δ * (Real.log Δ) ^ 2 / 2) :
    Real.logb 2 q ≤ Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) := by
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hlogpos : (0 : ℝ) < Real.log Δ := Real.log_pos hΔ
  have hpos : (0 : ℝ) < Δ * (Real.log Δ) ^ 2 / 2 := by positivity
  have hmono : Real.logb 2 q ≤ Real.logb 2 (Δ * (Real.log Δ) ^ 2 / 2) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hq hq_le
  have hmul : Real.logb 2 (Δ * (Real.log Δ) ^ 2 / 2)
      = Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) - 1 := by
    rw [Real.logb_div (by positivity : Δ * (Real.log Δ) ^ 2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
        Real.logb_mul (by linarith : Δ ≠ 0) (by positivity : (Real.log Δ) ^ 2 ≠ 0),
        Real.logb_pow]
    rw [show Real.logb 2 (2 : ℝ) = 1 from Real.logb_self_eq_one (by norm_num)]
    ring
  calc Real.logb 2 q ≤ Real.logb 2 (Δ * (Real.log Δ) ^ 2 / 2) := hmono
    _ = Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) - 1 := hmul
    _ ≤ Real.logb 2 Δ + 2 * Real.logb 2 (Real.log Δ) := by linarith

/-- Positive parameters `a` and `b` bounded by `sqrt Δ` satisfy `logb 2 a + logb 2 b + 2 ≤ logb
2 Δ + 2`. -/
theorem form_register_bits_bound {a b Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a) (hb : 0 < b)
    (haΔ : a ≤ Real.sqrt Δ) (hbΔ : b ≤ Real.sqrt Δ) :
    Real.logb 2 a + Real.logb 2 b + 2 ≤ Real.logb 2 Δ + 2 := by
  have hsq : Real.sqrt Δ = Δ ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Δ
  have hlog : Real.logb 2 (Real.sqrt Δ) = (1 / 2) * Real.logb 2 Δ := by
    rw [hsq, Real.logb_rpow_eq_mul_logb_of_pos hΔ]
  have ha' : Real.logb 2 a ≤ Real.logb 2 (Real.sqrt Δ) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ha haΔ
  have hb' : Real.logb 2 b ≤ Real.logb 2 (Real.sqrt Δ) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hb hbΔ
  have hsum : Real.logb 2 a + Real.logb 2 b ≤ Real.logb 2 Δ := by
    rw [hlog] at ha' hb'
    linarith
  linarith

end Qatlib.Papers.PrincIdeal09.MainResults
