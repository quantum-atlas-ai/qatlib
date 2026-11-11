/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Even bushes and transfer matrices

This module defines the bush response `bushY`, the transfer matrices, and a complex transmission
expression. It evaluates the bush response at `π / 2` according to parity and proves the
trigonometric formula for transfer-matrix powers and its unit-transmission consequence.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `bushY_at_three_even`: evaluates the even-depth response at `π / 2`.
* `transferA_pow`: computes powers of the transfer matrix when `sin θ` is nonzero.
* `transmission_one_of_all_y_one`: evaluates transmission for the explicit transfer-power
  entries.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Real

namespace Qatlib.Papers.DecisionTrees97.MainResults

/-- The trigonometric bush response ratio indexed by depth `k` and angle `θ`. -/
def bushY (k : ℕ) (θ : ℝ) : ℝ :=
  (1 / Real.sqrt 2) *
    ((Real.sqrt 2 * Real.sin (((k : ℝ) - 1) * θ) - Real.sin ((k : ℝ) * θ)) /
     (Real.sqrt 2 * Real.sin ((k : ℝ) * θ) - Real.sin (((k : ℝ) + 1) * θ)))

/-- Evaluates the sine of a natural multiple of `π` minus `π / 2` using parity. -/
private lemma sin_nat_mul_pi_sub_pi_div_two (j : ℕ) :
    Real.sin ((j : ℝ) * π - π / 2) = -(-1 : ℝ) ^ j := by
  rw [Real.sin_nat_mul_pi_sub, Real.sin_pi_div_two]
  ring

/-- Evaluates the sine of a natural multiple of `π` plus `π / 2` using parity. -/
private lemma sin_nat_mul_pi_add_pi_div_two (j : ℕ) :
    Real.sin ((j : ℝ) * π + π / 2) = (-1 : ℝ) ^ j := by
  rw [Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- At angle `π / 2`, the response of an even-depth bush is one. See [FarhiGutmann1998]. -/
theorem bushY_at_three_even (j : ℕ) : bushY (2 * j) (π / 2) = 1 := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hne : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have e1 : (((2 * j : ℕ) : ℝ) - 1) * (π / 2) = (j : ℝ) * π - π / 2 := by
    push_cast; ring
  have e2 : ((2 * j : ℕ) : ℝ) * (π / 2) = (j : ℝ) * π := by
    push_cast; ring
  have e3 : (((2 * j : ℕ) : ℝ) + 1) * (π / 2) = (j : ℝ) * π + π / 2 := by
    push_cast; ring
  unfold bushY
  rw [e1, e2, e3, sin_nat_mul_pi_sub_pi_div_two, Real.sin_nat_mul_pi,
    sin_nat_mul_pi_add_pi_div_two]
  have hratio : (Real.sqrt 2 * (-(-1 : ℝ) ^ j) - 0) /
      (Real.sqrt 2 * 0 - (-1 : ℝ) ^ j) = Real.sqrt 2 := by
    field_simp
    ring
  rw [hratio, one_div, inv_mul_cancel₀ hs2]

/-- At angle `π / 2`, the response of an odd-depth bush is minus one half. See
[FarhiGutmann1998]. -/
theorem bushY_at_three_odd (j : ℕ) : bushY (2 * j + 1) (π / 2) = -1 / 2 := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have e1 : (((2 * j + 1 : ℕ) : ℝ) - 1) * (π / 2) = (j : ℝ) * π := by
    push_cast; ring
  have e2 : (((2 * j + 1 : ℕ) : ℝ)) * (π / 2) = (j : ℝ) * π + π / 2 := by
    push_cast; ring
  have e3 : (((2 * j + 1 : ℕ) : ℝ) + 1) * (π / 2) = ((j + 1 : ℕ) : ℝ) * π := by
    push_cast; ring
  unfold bushY
  rw [e1, e2, e3, Real.sin_nat_mul_pi, sin_nat_mul_pi_add_pi_div_two,
    Real.sin_nat_mul_pi]
  have hratio : (Real.sqrt 2 * 0 - (-1 : ℝ) ^ j) /
      (Real.sqrt 2 * (-1 : ℝ) ^ j - 0) = -(1 / Real.sqrt 2) := by
    field_simp
    ring
  rw [hratio]
  field_simp
  rw [hsq]

/-- The two-by-two transfer matrix with first row `(3 - E - y, -1)` and second row `(1, 0)`. -/
def transferMatrix (E y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 - E - y, -1; 1, 0]

/-- The two-by-two transfer matrix with first row `(2 * cos θ, -1)` and second row `(1, 0)`. -/
def transferA (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * Real.cos θ, -1; 1, 0]

/-- The sine-ratio matrix giving the explicit expression for powers of `transferA` when `sin θ`
is nonzero. -/
def transferPow (n : ℕ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sin θ) •
    !![Real.sin (((n : ℝ) + 1) * θ), -Real.sin ((n : ℝ) * θ);
       Real.sin ((n : ℝ) * θ), -Real.sin (((n : ℝ) - 1) * θ)]

/-- For nonzero `sin θ`, the `n`th power of `transferA θ` equals `transferPow n θ`. See
[FarhiGutmann1998]. -/
theorem transferA_pow (n : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) :
    transferA θ ^ n = transferPow n θ := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [transferPow, pow_zero, Matrix.smul_apply, h]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [transferA, transferPow, Matrix.mul_apply, Matrix.smul_apply,
          Fin.sum_univ_two]
      · have e1 : ((n : ℝ) + 1 + 1) * θ = ((n : ℝ) + 1) * θ + θ := by ring
        have e2 : (n : ℝ) * θ = ((n : ℝ) + 1) * θ - θ := by ring
        rw [e1, e2, Real.sin_add, Real.sin_sub]
        ring
      · have e1 : ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ := by ring
        have e2 : ((n : ℝ) - 1) * θ = (n : ℝ) * θ - θ := by ring
        rw [e1, e2, Real.sin_add, Real.sin_sub]
        ring

/-- The complex transmission expression determined by the propagation length, angle, and four
transfer-matrix entries. -/
def transmission (n : ℕ) (θ a b c d : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (n : ℂ) * (θ : ℂ))) *
      (2 * Complex.I * (Real.sin θ : ℂ)) /
    (((c - b + (d - a) * Real.cos θ : ℝ) : ℂ)
      + Complex.I * (((d + a) * Real.sin θ : ℝ) : ℂ))

/-- Simplifies the real denominator expression for the explicit transfer-power entries to `2 *
sin θ * sin (n * θ)`. -/
private lemma re_identity (n : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) :
    (Real.sin ((n : ℝ) * θ) / Real.sin θ - (-Real.sin ((n : ℝ) * θ) / Real.sin θ)
      + (-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
          - Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.cos θ)
      = 2 * Real.sin θ * Real.sin ((n : ℝ) * θ) := by
  have e1 : ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ := by ring
  have e2 : ((n : ℝ) - 1) * θ = (n : ℝ) * θ - θ := by ring
  rw [e1, e2, Real.sin_add, Real.sin_sub]
  field_simp
  linear_combination (-2 * Real.sin ((n : ℝ) * θ)) * Real.sin_sq_add_cos_sq θ

/-- Simplifies the imaginary denominator expression for the explicit transfer-power entries to
`2 * sin θ * cos (n * θ)`. -/
private lemma im_identity (n : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) :
    ((-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
        + Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.sin θ)
      = 2 * Real.sin θ * Real.cos ((n : ℝ) * θ) := by
  have e1 : ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ := by ring
  have e2 : ((n : ℝ) - 1) * θ = (n : ℝ) * θ - θ := by ring
  rw [e1, e2, Real.sin_add, Real.sin_sub]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The transmission expression equals one for the explicit transfer-power entries when `sin θ`
is nonzero. See [FarhiGutmann1998]. -/
theorem transmission_one_of_all_y_one (n : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) :
    transmission n θ
      (Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ)
      (-Real.sin ((n : ℝ) * θ) / Real.sin θ)
      (Real.sin ((n : ℝ) * θ) / Real.sin θ)
      (-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ) = 1 := by
  have hre := re_identity n θ h
  have him := im_identity n θ h
  have hexp : Complex.exp (-(Complex.I * (n : ℂ) * (θ : ℂ)))
      = (Real.cos ((n : ℝ) * θ) : ℂ) - (Real.sin ((n : ℝ) * θ) : ℂ) * Complex.I := by
    have harg : -(Complex.I * (n : ℂ) * (θ : ℂ)) = ((-(((n : ℝ) * θ)) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hD : (((Real.sin ((n : ℝ) * θ) / Real.sin θ
        - (-Real.sin ((n : ℝ) * θ) / Real.sin θ)
        + (-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
            - Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.cos θ : ℝ) : ℂ)
      + Complex.I * (((-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
            + Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.sin θ : ℝ) : ℂ))
      = Complex.exp (-(Complex.I * (n : ℂ) * (θ : ℂ))) *
          (2 * Complex.I * (Real.sin θ : ℂ)) := by
    have hre' : (((Real.sin ((n : ℝ) * θ) / Real.sin θ
          - (-Real.sin ((n : ℝ) * θ) / Real.sin θ)
          + (-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
              - Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.cos θ : ℝ)) : ℂ)
        = ((2 * Real.sin θ * Real.sin ((n : ℝ) * θ) : ℝ) : ℂ) := by rw [hre]
    have him' : ((((-Real.sin (((n : ℝ) - 1) * θ) / Real.sin θ
              + Real.sin (((n : ℝ) + 1) * θ) / Real.sin θ) * Real.sin θ : ℝ)) : ℂ)
        = ((2 * Real.sin θ * Real.cos ((n : ℝ) * θ) : ℝ) : ℂ) := by rw [him]
    rw [hre', him', hexp]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.I_re, Complex.I_im] <;>
      ring
  unfold transmission
  rw [hD]
  have hnum : Complex.exp (-(Complex.I * (n : ℂ) * (θ : ℂ))) *
      (2 * Complex.I * (Real.sin θ : ℂ)) ≠ 0 := by
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero (by norm_num)
    exact_mod_cast h
  exact div_self hnum

end Qatlib.Papers.DecisionTrees97.MainResults
