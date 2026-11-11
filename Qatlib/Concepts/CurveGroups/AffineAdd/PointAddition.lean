/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Arithmetic schedule for affine point addition

This module defines the secant formulas `slope`, `addX`, and `addY`, together with the
controlled arithmetic register schedule `run`. It proves the coordinate outputs for both control
values and auxiliary register cleanup under the second inversion condition. The schedule is
based on the affine arithmetic setting of [RoettelerEtAl2017].

## Main statements

* `alg1_ctrl_true`: enabled coordinate correctness.
* `alg1_ctrl_false`: disabled coordinate preservation.
* `alg1_ancillas_cleared`: cleanup under both inversion conditions.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

variable {K : Type*} [Field K]

/-- The secant slope `(y1 - y2) / (x1 - x2)` in the field. -/
def slope (x1 y1 x2 y2 : K) : K := (y1 - y2) / (x1 - x2)

/-- The affine addition X coordinate `lam ^ 2 - x1 - x2`. -/
def addX (x1 x2 : K) (lam : K) : K := lam ^ 2 - x1 - x2

/-- The affine addition Y coordinate `(x1 - x3) * lam - y1`. -/
def addY (x1 y1 x3 : K) (lam : K) : K := (x1 - x3) * lam - y1

/-- Field registers for two affine coordinates, a slope, and a temporary value. -/
structure Reg (K : Type*) [Field K] where

  x1 : K

  y1 : K

  lam : K

  t0 : K

/-- Evaluate the controlled affine point addition arithmetic schedule with zero initial
auxiliary registers. -/
def run (ctrl : Bool) (x2 y2 x1 y1 : K) : Reg K :=
  let x1₁ := x1 - x2
  let y1₂ := if ctrl then y1 - y2 else y1
  let t0₃ := x1₁⁻¹ - 0
  let lam₄ := y1₂ * t0₃ - 0
  let y1₅ := lam₄ * x1₁ - y1₂
  let t0₆ := x1₁⁻¹ - t0₃
  let t0₇ := lam₄ ^ 2 - t0₆
  let x1₈ := if ctrl then x1₁ - t0₇ else x1₁
  let x1₉ := if ctrl then x1₈ + 3 * x2 else x1₈
  let t0₁₀ := lam₄ ^ 2 - t0₇
  let y1₁₁ := lam₄ * x1₉ - y1₅
  let t0₁₂ := x1₉⁻¹ - t0₁₀
  let lam₁₃ := t0₁₂ * y1₁₁ - lam₄
  let t0₁₄ := x1₉⁻¹ - t0₁₂
  let x1₁₅ := if ctrl then -x1₉ else x1₉
  let y1₁₆ := if ctrl then y1₁₁ - y2 else y1₁₁
  ⟨x1₁₅ + x2, y1₁₆, lam₁₃, t0₁₄⟩

/-- When the X coordinates differ, the enabled schedule returns the secant addition coordinates. -/
theorem alg1_ctrl_true {x1 y1 x2 y2 : K} (h : x1 ≠ x2) :
    (run true x2 y2 x1 y1).x1 = addX x1 x2 (slope x1 y1 x2 y2) ∧
    (run true x2 y2 x1 y1).y1 =
      addY x1 y1 (addX x1 x2 (slope x1 y1 x2 y2)) (slope x1 y1 x2 y2) := by
  unfold run slope addX addY
  simp only [if_true]
  have h' : x1 - x2 ≠ 0 := sub_ne_zero.mpr h
  constructor <;> field_simp <;> ring

/-- When the X coordinates differ, the disabled schedule preserves both input coordinates. -/
theorem alg1_ctrl_false {x1 y1 x2 y2 : K} (h : x1 ≠ x2) :
    (run false x2 y2 x1 y1).x1 = x1 ∧ (run false x2 y2 x1 y1).y1 = y1 := by
  unfold run
  simp only [Bool.false_eq_true, if_false]
  have h' : x1 - x2 ≠ 0 := sub_ne_zero.mpr h
  constructor
  · ring
  · field_simp
    ring

/-- The enabled schedule clears the slope and temporary registers when the X coordinates differ
and the sum X coordinate differs from `x2`. -/
theorem alg1_ancillas_cleared {x1 y1 x2 y2 : K} (h : x1 ≠ x2)
    (hx : x2 ≠ addX x1 x2 (slope x1 y1 x2 y2)) :
    (run true x2 y2 x1 y1).lam = 0 ∧ (run true x2 y2 x1 y1).t0 = 0 := by
  unfold run slope addX at *
  simp only [if_true, sub_zero, sub_self]
  rw [div_eq_mul_inv] at hx
  have h' : x1 - x2 ≠ 0 := sub_ne_zero.mpr h
  set D := x1 - x2 with hD
  set S := (y1 - y2) * D⁻¹ with hS
  set X := (D - S ^ 2) + 3 * x2 with hX
  have hSD : S * D = y1 - y2 := by
    rw [hS, mul_assoc, inv_mul_cancel₀ h', mul_one]
  have hX0 : X ≠ 0 := by
    intro hz
    apply hx
    rw [hS, hD]
    rw [hX, hS, hD] at hz
    linear_combination hz
  have h5 : S * D - (y1 - y2) = 0 := by rw [hSD]; ring
  have hXinv : X⁻¹ * (S * X) = S := by
    rw [mul_comm (X⁻¹) (S * X), mul_assoc, mul_comm X X⁻¹, inv_mul_cancel₀ hX0, mul_one]
  constructor
  · rw [h5, sub_zero, hXinv, sub_self]
  · first | ring | trivial

end Qatlib.Concepts.CurveGroups.AffineAdd
