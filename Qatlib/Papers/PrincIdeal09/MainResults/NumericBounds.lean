/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.PrincIdeal09.MainResults

theorem six_div_pi_sq_gt_half : (1 / 2 : ℝ) < 6 / Real.pi ^ 2 := by
  have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsq : Real.pi ^ 2 < 12 := by nlinarith [hpi_lt, hpi_pos]
  have hpos : 0 < Real.pi ^ 2 := by positivity
  rw [lt_div_iff₀ hpos]
  nlinarith [hsq]

theorem thm2_prob_bound : (2 : ℝ) ^ (-26 : ℤ) ≤ (6 / Real.pi ^ 2) * (2 : ℝ) ^ (-25 : ℤ) := by
  have h := six_div_pi_sq_gt_half
  have h2 : (2 : ℝ) ^ (-25 : ℤ) = 2 * (2 : ℝ) ^ (-26 : ℤ) := by
    rw [show (-25 : ℤ) = -26 + 1 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_one]; ring
  rw [h2]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-26 : ℤ) := by positivity
  nlinarith [h, hpos]

theorem thm4_prob_bound : (2 : ℝ) ^ (-37 : ℤ) ≤ (6 / Real.pi ^ 2) * (2 : ℝ) ^ (-35 : ℤ) := by
  have h := six_div_pi_sq_gt_half
  have h2 : (2 : ℝ) ^ (-35 : ℤ) = 4 * (2 : ℝ) ^ (-37 : ℤ) := by
    rw [show (-35 : ℤ) = -37 + 2 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [zpow_two]; ring
  rw [h2]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-37 : ℤ) := by positivity
  nlinarith [h, hpos]

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

theorem logb_two_ten_le_five : Real.logb 2 10 ≤ 5 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 10)]
  norm_num

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
