/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3

/-!
# Active-learning reflection cost bounds

This module bounds the geometric attempt scale and the separate diffusion and checking costs in
the quantum reflecting procedure of [PaparoEtAl2014]. Under the explicit angle and
primitive-cost bounds, `quantum_rps_total_cost` gives a total bound with constant 99, and the
final identities compare inverse-square-root and inverse classical count scales.

## Main statements

* `quantum_rps_total_cost`: a total cost bound in the marked mass and spectral gap.
* `diffusion_calls_bound`: the diffusion contribution.
* `check_calls_bound`: the checking contribution.

## References

* [Paparo et al., 2014][PaparoEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QActiveLearn14.CostModels

open scoped BigOperators

/-- Under the stated attempt-angle and primitive-cost assumptions, the total cost is at most `99
* (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C)` [PaparoEtAl2014]. -/
theorem quantum_rps_total_cost
    (ε c₁ c₂ U C δ : ℝ) (tMax : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * Real.pi / 4)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hcU : c₁ ≤ 2 * U / Real.sqrt δ) (hcc : c₂ ≤ C) :
    2 * (3 : ℝ) ^ tMax * (c₁ * (Real.log 72 + 3) + c₂) ≤
      99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) :=
  Qatlib.Concepts.WalkSearch.MnrsAmplify.mnrs_order_form_cost
    ε c₁ c₂ U C δ tMax hε hε1 hc₁ hc₂ hmax hδ hC hcU hcc

/-- The natural logarithm of 72 is at most five. -/
theorem log_seventy_two_le_five : Real.log 72 ≤ 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 72)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 6
  norm_num [Finset.sum_range_succ] at hs
  linarith only [hs]

/-- For positive `ε ≤ 1`, the stated upper bound on the amplified angle implies `2 * 3 ^ tMax ≤
5 / Real.sqrt ε`. -/
theorem attempt_scale (ε : ℝ) (tMax : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * Real.pi / 4) :
    2 * (3 : ℝ) ^ tMax ≤ 5 / Real.sqrt ε := by
  have hrε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hroot1 : Real.sqrt ε ≤ 1 := by simpa using Real.sqrt_le_sqrt hε1
  have ha0 : 0 ≤ Real.arcsin (Real.sqrt ε) := (Real.arcsin_pos.mpr hrε).le
  have hsin : Real.sin (Real.arcsin (Real.sqrt ε)) = Real.sqrt ε :=
    Real.sin_arcsin (by linarith [hrε]) hroot1
  have hroot_angle : Real.sqrt ε ≤ Real.arcsin (Real.sqrt ε) := by
    simpa only [hsin] using Real.sin_le ha0
  apply (le_div_iff₀ hrε).mpr
  have he := mul_le_mul_of_nonneg_left hroot_angle (by positivity : (0 : ℝ) ≤ 3 ^ tMax)
  nlinarith only [he, hmax, Real.pi_lt_d2]

/-- The diffusion contribution is at most `99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)`
under the stated angle and diffusion-cost bounds. -/
theorem diffusion_calls_bound
    (ε c₁ c₂ U C δ : ℝ) (tMax : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * Real.pi / 4)
    (hδ : 0 < δ) (_hC : 0 ≤ C) (hcU : c₁ ≤ 2 * U / Real.sqrt δ) (_hcc : c₂ ≤ C) :
    2 * (3 : ℝ) ^ tMax * c₁ * (Real.log 72 + 3) ≤
      99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U) := by
  have hscale := attempt_scale ε tMax hε hε1 hmax
  have hrε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hrδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hU : 0 ≤ U := by
    have hmul : c₁ * Real.sqrt δ ≤ 2 * U := by
      have h := (le_div_iff₀ hrδ).mp hcU
      nlinarith [h]
    nlinarith [hmul, hc₁, Real.sqrt_nonneg δ]
  have hlog8 : Real.log 72 + 3 ≤ 8 := by
    have := log_seventy_two_le_five
    linarith
  have hwalk : c₁ * (Real.log 72 + 3) ≤ 16 * (U / Real.sqrt δ) := by
    calc c₁ * (Real.log 72 + 3) ≤ c₁ * 8 := mul_le_mul_of_nonneg_left hlog8 hc₁
      _ ≤ (2 * U / Real.sqrt δ) * 8 := mul_le_mul_of_nonneg_right hcU (by norm_num)
      _ = 16 * (U / Real.sqrt δ) := by ring
  have hstep : 2 * (3 : ℝ) ^ tMax * c₁ * (Real.log 72 + 3) ≤
      (5 / Real.sqrt ε) * (16 * (U / Real.sqrt δ)) := by
    have heq : 2 * (3 : ℝ) ^ tMax * c₁ * (Real.log 72 + 3) =
        (2 * (3 : ℝ) ^ tMax) * (c₁ * (Real.log 72 + 3)) := by ring
    rw [heq]
    exact mul_le_mul hscale hwalk (by positivity) (by positivity)
  have hval : (5 / Real.sqrt ε) * (16 * (U / Real.sqrt δ)) =
      80 * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) := by
    field_simp
    ring
  have hgoal : 99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U) =
      99 * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) := by ring
  calc 2 * (3 : ℝ) ^ tMax * c₁ * (Real.log 72 + 3)
      ≤ (5 / Real.sqrt ε) * (16 * (U / Real.sqrt δ)) := hstep
    _ = 80 * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) := hval
    _ ≤ 99 * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U) := hgoal.symm

/-- The checking contribution is at most `99 * (1 / Real.sqrt ε) * C` under the stated angle and
checking-cost bounds. -/
theorem check_calls_bound
    (ε c₁ c₂ U C δ : ℝ) (tMax : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (_hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * Real.pi / 4)
    (_hδ : 0 < δ) (hC : 0 ≤ C) (_hcU : c₁ ≤ 2 * U / Real.sqrt δ) (hcc : c₂ ≤ C) :
    2 * (3 : ℝ) ^ tMax * c₂ ≤ 99 * (1 / Real.sqrt ε) * C := by
  have hscale := attempt_scale ε tMax hε hε1 hmax
  have hrε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hstep : 2 * (3 : ℝ) ^ tMax * c₂ ≤ (5 / Real.sqrt ε) * C :=
    mul_le_mul hscale hcc hc₂ (by positivity)
  have hval : (5 / Real.sqrt ε) * C = 5 * ((1 / Real.sqrt ε) * C) := by
    field_simp
  have hgoal : 99 * (1 / Real.sqrt ε) * C = 99 * ((1 / Real.sqrt ε) * C) := by ring
  calc 2 * (3 : ℝ) ^ tMax * c₂ ≤ (5 / Real.sqrt ε) * C := hstep
    _ = 5 * ((1 / Real.sqrt ε) * C) := hval
    _ ≤ 99 * ((1 / Real.sqrt ε) * C) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 99 * (1 / Real.sqrt ε) * C := hgoal.symm

/-- For positive marked mass and gap, the inverse product equals the square of its
inverse-square-root scale. -/
theorem classical_count_eq_quantum_count_sq {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    1 / (ε * δ) = (1 / Real.sqrt (ε * δ)) ^ 2 := by
  have h : Real.sqrt (ε * δ) ^ 2 = ε * δ := Real.sq_sqrt (le_of_lt (mul_pos hε hδ))
  rw [div_pow, one_pow, h]

/-- For marked mass and gap in `(0, 1]`, the inverse-square-root count scale is at most the
inverse-product count scale. -/
theorem quantum_count_le_classical {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hε1 : ε ≤ 1) (hδ1 : δ ≤ 1) :
    1 / Real.sqrt (ε * δ) ≤ 1 / (ε * δ) := by
  have hx : 0 < ε * δ := mul_pos hε hδ
  have hx1 : ε * δ ≤ 1 := by
    have := mul_le_mul hε1 hδ1 hδ.le zero_le_one
    simpa using this
  have hs1 : Real.sqrt (ε * δ) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hx1
  have hsq : Real.sqrt (ε * δ) * Real.sqrt (ε * δ) = ε * δ := Real.mul_self_sqrt hx.le
  have hs0 : 0 ≤ Real.sqrt (ε * δ) := Real.sqrt_nonneg _
  have hxle : ε * δ ≤ Real.sqrt (ε * δ) := by nlinarith [hs1, hs0, hsq]
  exact one_div_le_one_div_of_le hx hxle

end Qatlib.Papers.QActiveLearn14.CostModels
