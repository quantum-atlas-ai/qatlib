/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalSmoothness

/-!
# Pointwise decay and energy density of the rational Bateman field

[Kedia2013TyingKnots], equation (6) and p150404-2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The companion of `Qatlib.Papers.KnotLight13.TorusFamily.RationalSmoothness`:
the energy content of the smooth Bateman field `F = ∇α × ∇β` of the explicit
rational pair is established through an explicit pointwise decay bound
`‖F j‖² ≤ 14745600 (1 + t²) ^ 12 / (1 + x² + y² + z²) ^ 4`, built from
polynomial majorants of the gradient numerators and a strictly positive lower
bound on the squared modulus of the common denominator, together with the
identification of the energy density `∑ j, ‖F j‖²` with the paper's
`|E|² + |B|²`. The companion module
`Qatlib.Papers.KnotLight13.TorusFamily.RationalEnergy` uses this bound to
establish spatial integrability. No field-line geometry, helicity value, or
topological statement is claimed here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux pairDenominator
  pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)

/-! ### Norm-square helpers and the polynomial majorant -/

/-- The squared modulus of a sum is at most twice the sum of squared moduli,
by componentwise Cauchy estimates in the real and imaginary parts. -/
theorem normSq_add_le (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply,
    Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

/-- The squared modulus of a difference is at most twice the sum of squared
moduli. -/
theorem normSq_sub_le (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  have h : Complex.normSq (z + (-w)) ≤
      2 * (Complex.normSq z + Complex.normSq (-w)) :=
    normSq_add_le _ _
  rwa [Complex.normSq_neg] at h

/-- The squared modulus of a real number coerced to the complex plane is its
square. -/
theorem normSq_ofReal (x : ℝ) : Complex.normSq ((x : ℂ)) = x * x := by
  rw [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The squared modulus of the imaginary unit is one. -/
theorem normSq_I : Complex.normSq Complex.I = 1 := by
  rw [Complex.normSq_apply, Complex.I_re, Complex.I_im]
  norm_num

/-- The squared modulus of the numeral `4` is sixteen. -/
theorem normSq_four : Complex.normSq ((4 : ℂ)) = 16 := by
  rw [Complex.normSq_apply]
  norm_num

/-- The squared modulus of the numeral `2` is four. -/
theorem normSq_two : Complex.normSq ((2 : ℂ)) = 4 := by
  rw [Complex.normSq_apply]
  norm_num

/-- The degree-two polynomial majorant `1 + x² + y² + z² + t²`. -/
noncomputable def majorantSum (x y z t : ℝ) : ℝ := 1 + x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2

/-- The majorant dominates `x²`. -/
theorem sq_le_majorantSum_x (x y z t : ℝ) :
    x * x ≤ majorantSum x y z t := by
  simp only [majorantSum]
  nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg t]

/-- The majorant dominates `y²`. -/
theorem sq_le_majorantSum_y (x y z t : ℝ) :
    y * y ≤ majorantSum x y z t := by
  simp only [majorantSum]
  nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg t]

/-- The majorant dominates `z²`. -/
theorem sq_le_majorantSum_z (x y z t : ℝ) :
    z * z ≤ majorantSum x y z t := by
  simp only [majorantSum]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg t]

/-- The majorant dominates `t²`. -/
theorem sq_le_majorantSum_t (x y z t : ℝ) :
    t * t ≤ majorantSum x y z t := by
  simp only [majorantSum]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- The majorant is at least one everywhere. -/
theorem one_le_majorantSum (x y z t : ℝ) : (1 : ℝ) ≤ majorantSum x y z t := by
  simp only [majorantSum]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]

/-- The majorant is nonnegative. -/
theorem majorantSum_nonneg (x y z t : ℝ) : (0 : ℝ) ≤ majorantSum x y z t :=
  le_trans (by positivity : (0 : ℝ) ≤ 1) (one_le_majorantSum x y z t)

/-- The absolute value of the auxiliary radius is dominated by the majorant. -/
theorem abs_radialAux_le (x y z t : ℝ) :
    |radialAux x y z t| ≤ majorantSum x y z t := by
  simp only [radialAux, majorantSum]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]

/-- The square of the auxiliary radius is dominated by the squared majorant. -/
theorem radialAux_sq_le_majorant (x y z t : ℝ) :
    radialAux x y z t * radialAux x y z t ≤
      majorantSum x y z t * majorantSum x y z t := by
  have h1 : |radialAux x y z t| * |radialAux x y z t| ≤
      |radialAux x y z t| * majorantSum x y z t :=
    mul_le_mul_of_nonneg_left (abs_radialAux_le x y z t) (abs_nonneg _)
  have h2 : |radialAux x y z t| * majorantSum x y z t ≤
      majorantSum x y z t * majorantSum x y z t :=
    mul_le_mul_of_nonneg_right (abs_radialAux_le x y z t)
      (majorantSum_nonneg x y z t)
  calc radialAux x y z t * radialAux x y z t
      = |radialAux x y z t| * |radialAux x y z t| :=
        (abs_mul_abs_self _).symm
    _ ≤ |radialAux x y z t| * majorantSum x y z t := h1
    _ ≤ majorantSum x y z t * majorantSum x y z t := h2

/-- The squared modulus of the common factor is dominated by five majorants. -/
theorem normSq_alphaCommonFactor_le (x y z t : ℝ) :
    Complex.normSq (alphaCommonFactor z t) ≤ 5 * majorantSum x y z t := by
  have h : Complex.normSq (alphaCommonFactor z t) = 1 + (t - z) * (t - z) := by
    simp only [alphaCommonFactor, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [h]
  simp only [majorantSum]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t,
    sq_nonneg (t - z)]

/-- The squared modulus of the reduced β numerator is the planar radius
squared. -/
theorem normSq_betaReducedNumerator (x y : ℝ) :
    Complex.normSq (betaReducedNumerator x y) = x * x + y * y := by
  rw [Complex.normSq_apply, betaReducedNumerator]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The squared modulus of the common denominator equals `pairDenominator`. -/
theorem normSq_complexDenominator (x y z t : ℝ) :
    Complex.normSq (complexDenominator x y z t) = pairDenominator x y z t := by
  rw [Complex.normSq_apply, complexDenominator]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    pairDenominator, radialAux, pow_two]
  ring

/-- The pair denominator is dominated by the squared majorant plus four
majorants. -/
theorem pairDenominator_le_majorant (x y z t : ℝ) :
    pairDenominator x y z t ≤
      majorantSum x y z t ^ 2 + 4 * majorantSum x y z t := by
  have hpd : pairDenominator x y z t =
      radialAux x y z t * radialAux x y z t + 4 * (t * t) := by
    simp only [pairDenominator]
    ring
  have hA2 := radialAux_sq_le_majorant x y z t
  have ht := sq_le_majorantSum_t x y z t
  rw [hpd]
  linarith

/-- The denominator lower bound: the squared modulus of `w` dominates
`(1 + x² + y² + z²)²` divided by `4 (1 + t²)²`, in multiplication form. -/
theorem pairDenominator_lower (x y z t : ℝ) :
    (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≤
      4 * (1 + t ^ 2) ^ 2 * pairDenominator x y z t := by
  have hpd : pairDenominator x y z t =
      ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) ^ 2 + 4 * t ^ 2 := by
    simp only [pairDenominator, radialAux]
    ring
  have hsplit : 4 * (1 + t ^ 2) ^ 2 *
      (((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) ^ 2 + 4 * t ^ 2) =
      4 * (1 + t ^ 2) ^ 2 * ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) ^ 2 +
      16 * t ^ 2 * (1 + t ^ 2) ^ 2 := by ring
  have hA : (0 : ℝ) ≤ 4 * (1 + t ^ 2) ^ 2 *
      ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) ^ 2 := by positivity
  have hv0 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have hiv : (1 : ℝ) ≤ (1 + t ^ 2) * (1 + t ^ 2) := by nlinarith [hv0]
  have hu1 : (1 : ℝ) ≤ 1 + x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  rw [hpd, hsplit]
  rcases le_or_gt (t ^ 2) ((1 + x ^ 2 + y ^ 2 + z ^ 2) / 2) with hcase | hcase
  · have hA1 : 1 + x ^ 2 + y ^ 2 + z ^ 2 ≤
        2 * ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) := by linarith
    have hA10 : (0 : ℝ) ≤ (1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2 := by linarith
    have e1 : (1 + x ^ 2 + y ^ 2 + z ^ 2) * (1 + x ^ 2 + y ^ 2 + z ^ 2) ≤
        4 * ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) *
          ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) := by
      nlinarith [hA1, hA10]
    have h2 : ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) *
        ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) * (1 : ℝ) ≤
        ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) *
          ((1 + x ^ 2 + y ^ 2 + z ^ 2) - t ^ 2) * ((1 + t ^ 2) * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hiv (by positivity)
    have h3 : (0 : ℝ) ≤ t ^ 2 * ((1 + t ^ 2) * (1 + t ^ 2)) := by positivity
    linarith [e1, h2, h3, hA]
  · have hu2 : 1 + x ^ 2 + y ^ 2 + z ^ 2 < 2 * t ^ 2 := by linarith
    have hu0 : (0 : ℝ) ≤ 1 + x ^ 2 + y ^ 2 + z ^ 2 := by linarith
    have e1 : (1 + x ^ 2 + y ^ 2 + z ^ 2) * (1 + x ^ 2 + y ^ 2 + z ^ 2) ≤
        (2 * t ^ 2) * (2 * t ^ 2) := by
      have hut2 : 1 + x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * t ^ 2 := le_of_lt hu2
      have hprod : (1 + x ^ 2 + y ^ 2 + z ^ 2) * (t * t) ≤ (2 * t ^ 2) * (t * t) :=
        mul_le_mul hut2 (le_refl (t * t)) (by nlinarith [sq_nonneg t])
          (by positivity)
      have hu2sq : (1 + x ^ 2 + y ^ 2 + z ^ 2) * (1 + x ^ 2 + y ^ 2 + z ^ 2) ≤
          (2 * t ^ 2) * (1 + x ^ 2 + y ^ 2 + z ^ 2) :=
        mul_le_mul_of_nonneg_right hut2 hu0
      nlinarith [hprod, hu2sq]
    have e2 : (2 * t ^ 2) * (2 * t ^ 2) ≤
        16 * t ^ 2 * ((1 + t ^ 2) * (1 + t ^ 2)) := by
      nlinarith [hv0, sq_nonneg (2 * t ^ 2 - 1)]
    linarith [e1, e2, hA]

/-! ### Pointwise majorants of the gradient numerators -/

/-- The x-numerator of α is dominated by eighty squared majorants. -/
theorem normSq_alphaXNumerator_le (x y z t : ℝ) :
    Complex.normSq (alphaXNumerator x y z t) ≤ 80 * majorantSum x y z t ^ 2 := by
  have hsplit : Complex.normSq (alphaXNumerator x y z t) =
      Complex.normSq ((4 : ℂ) * (x : ℂ)) * Complex.normSq (alphaCommonFactor z t) := by
    rw [alphaXNumerator, Complex.normSq_mul]
  have h4 : Complex.normSq ((4 : ℂ) * (x : ℂ)) = 16 * (x * x) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hg := normSq_alphaCommonFactor_le x y z t
  have hx := sq_le_majorantSum_x x y z t
  have hprod : Complex.normSq (alphaCommonFactor z t) * (x * x) ≤
      5 * majorantSum x y z t * majorantSum x y z t :=
    mul_le_mul hg hx (by nlinarith [sq_nonneg x])
      (by linarith [majorantSum_nonneg x y z t])
  rw [hsplit, h4]
  linarith [hprod]

/-- The y-numerator of α is dominated by eighty squared majorants. -/
theorem normSq_alphaYNumerator_le (x y z t : ℝ) :
    Complex.normSq (alphaYNumerator x y z t) ≤ 80 * majorantSum x y z t ^ 2 := by
  have hsplit : Complex.normSq (alphaYNumerator x y z t) =
      Complex.normSq ((4 : ℂ) * (y : ℂ)) * Complex.normSq (alphaCommonFactor z t) := by
    rw [alphaYNumerator, Complex.normSq_mul]
  have h4 : Complex.normSq ((4 : ℂ) * (y : ℂ)) = 16 * (y * y) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hg := normSq_alphaCommonFactor_le x y z t
  have hy := sq_le_majorantSum_y x y z t
  have hprod : Complex.normSq (alphaCommonFactor z t) * (y * y) ≤
      5 * majorantSum x y z t * majorantSum x y z t :=
    mul_le_mul hg hy (by nlinarith [sq_nonneg y])
      (by linarith [majorantSum_nonneg x y z t])
  rw [hsplit, h4]
  linarith [hprod]

/-- The z-numerator of α is dominated by two hundred squared majorants. -/
theorem normSq_alphaZNumerator_le (x y z t : ℝ) :
    Complex.normSq (alphaZNumerator x y z t) ≤ 200 * majorantSum x y z t ^ 2 := by
  have hsplit : Complex.normSq (alphaZNumerator x y z t) ≤
      2 * (Complex.normSq ((4 : ℂ) * (z : ℂ) * alphaCommonFactor z t) +
        Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t)) := by
    rw [alphaZNumerator]
    exact normSq_add_le _ _
  have h4z : Complex.normSq ((4 : ℂ) * (z : ℂ)) = 16 * (z * z) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hz := sq_le_majorantSum_z x y z t
  have hg := normSq_alphaCommonFactor_le x y z t
  have h1 : Complex.normSq ((4 : ℂ) * (z : ℂ) * alphaCommonFactor z t) ≤
      80 * majorantSum x y z t ^ 2 := by
    have hprod : Complex.normSq (alphaCommonFactor z t) * (z * z) ≤
        5 * majorantSum x y z t * majorantSum x y z t :=
      mul_le_mul hg hz (by nlinarith [sq_nonneg z])
        (by linarith [majorantSum_nonneg x y z t])
    rw [Complex.normSq_mul, h4z]
    linarith [hprod]
  have hw : Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t) =
      4 * pairDenominator x y z t := by
    rw [Complex.normSq_mul, Complex.normSq_mul, normSq_two, normSq_I,
      normSq_complexDenominator]
    ring
  have hpdl := pairDenominator_le_majorant x y z t
  have hS := one_le_majorantSum x y z t
  have hSS : majorantSum x y z t ≤ majorantSum x y z t ^ 2 := by
    nlinarith [hS, majorantSum_nonneg x y z t]
  have h2 : Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t) ≤
      20 * majorantSum x y z t ^ 2 := by
    rw [hw]
    linarith
  linarith [hsplit, h1, h2]

/-- The x-numerator of β is dominated by seventy-two squared majorants. -/
theorem normSq_betaXNumerator_le (x y z t : ℝ) :
    Complex.normSq (betaXNumerator x y z t) ≤ 72 * majorantSum x y z t ^ 2 := by
  have hsplit : Complex.normSq (betaXNumerator x y z t) ≤
      2 * (Complex.normSq ((2 : ℂ) * complexDenominator x y z t) +
        Complex.normSq ((4 : ℂ) * (x : ℂ) * betaReducedNumerator x y)) := by
    rw [betaXNumerator]
    exact normSq_sub_le _ _
  have hw : Complex.normSq ((2 : ℂ) * complexDenominator x y z t) =
      4 * pairDenominator x y z t := by
    rw [Complex.normSq_mul, normSq_two, normSq_complexDenominator]
  have h4x : Complex.normSq ((4 : ℂ) * (x : ℂ)) = 16 * (x * x) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hbr := normSq_betaReducedNumerator x y
  have hS := one_le_majorantSum x y z t
  have hx := sq_le_majorantSum_x x y z t
  have hpdl := pairDenominator_le_majorant x y z t
  have hSS : majorantSum x y z t ≤ majorantSum x y z t ^ 2 := by
    nlinarith [hS, majorantSum_nonneg x y z t]
  have h1 : Complex.normSq ((2 : ℂ) * complexDenominator x y z t) ≤
      20 * majorantSum x y z t ^ 2 := by
    rw [hw]
    linarith
  have h2 : Complex.normSq ((4 : ℂ) * (x : ℂ) * betaReducedNumerator x y) ≤
      16 * majorantSum x y z t ^ 2 := by
    have hxy : x * x + y * y ≤ majorantSum x y z t := by
      simp only [majorantSum]
      nlinarith [sq_nonneg z, sq_nonneg t]
    have hprod : (x * x) * ((x * x) + (y * y)) ≤
        majorantSum x y z t * majorantSum x y z t :=
      mul_le_mul hx hxy (by nlinarith [sq_nonneg x, sq_nonneg y])
        (majorantSum_nonneg x y z t)
    rw [Complex.normSq_mul, h4x, hbr]
    linarith [hprod]
  linarith [hsplit, h1, h2]

/-- The y-numerator of β is dominated by seventy-two squared majorants. -/
theorem normSq_betaYNumerator_le (x y z t : ℝ) :
    Complex.normSq (betaYNumerator x y z t) ≤ 72 * majorantSum x y z t ^ 2 := by
  have hsplit : Complex.normSq (betaYNumerator x y z t) ≤
      2 * (Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t) +
        Complex.normSq ((4 : ℂ) * (y : ℂ) * betaReducedNumerator x y)) := by
    have h := normSq_add_le (-(2 * Complex.I * complexDenominator x y z t))
      (-(4 * (y : ℂ) * betaReducedNumerator x y))
    rw [Complex.normSq_neg, Complex.normSq_neg] at h
    have hbb : betaYNumerator x y z t =
        -(2 * Complex.I * complexDenominator x y z t) +
          -(4 * (y : ℂ) * betaReducedNumerator x y) := by
      rw [betaYNumerator]
      ring
    rw [hbb]
    exact h
  have hw : Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t) =
      4 * pairDenominator x y z t := by
    rw [Complex.normSq_mul, Complex.normSq_mul, normSq_two, normSq_I,
      normSq_complexDenominator]
    ring
  have h4y : Complex.normSq ((4 : ℂ) * (y : ℂ)) = 16 * (y * y) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hbr := normSq_betaReducedNumerator x y
  have hS := one_le_majorantSum x y z t
  have hy := sq_le_majorantSum_y x y z t
  have hpdl := pairDenominator_le_majorant x y z t
  have hSS : majorantSum x y z t ≤ majorantSum x y z t ^ 2 := by
    nlinarith [hS, majorantSum_nonneg x y z t]
  have h1 : Complex.normSq ((2 : ℂ) * Complex.I * complexDenominator x y z t) ≤
      20 * majorantSum x y z t ^ 2 := by
    rw [hw]
    linarith
  have h2 : Complex.normSq ((4 : ℂ) * (y : ℂ) * betaReducedNumerator x y) ≤
      16 * majorantSum x y z t ^ 2 := by
    have hxy : x * x + y * y ≤ majorantSum x y z t := by
      simp only [majorantSum]
      nlinarith [sq_nonneg z, sq_nonneg t]
    have hprod : (y * y) * ((x * x) + (y * y)) ≤
        majorantSum x y z t * majorantSum x y z t :=
      mul_le_mul hy hxy (by nlinarith [sq_nonneg x, sq_nonneg y])
        (majorantSum_nonneg x y z t)
    rw [Complex.normSq_mul, h4y, hbr]
    linarith [hprod]
  linarith [hsplit, h1, h2]

/-- The z-numerator of β is dominated by seventy-two squared majorants. -/
theorem normSq_betaZNumerator_le (x y z t : ℝ) :
    Complex.normSq (betaZNumerator x y z t) ≤ 72 * majorantSum x y z t ^ 2 := by
  have h4z : Complex.normSq ((4 : ℂ) * (z : ℂ)) = 16 * (z * z) := by
    rw [Complex.normSq_mul, normSq_four, normSq_ofReal]
  have hbr := normSq_betaReducedNumerator x y
  have hz := sq_le_majorantSum_z x y z t
  have hxy : x * x + y * y ≤ majorantSum x y z t := by
    simp only [majorantSum]
    nlinarith [sq_nonneg z, sq_nonneg t]
  have hprod : (z * z) * ((x * x) + (y * y)) ≤
      majorantSum x y z t * majorantSum x y z t :=
    mul_le_mul hz hxy (by nlinarith [sq_nonneg x, sq_nonneg y])
      (majorantSum_nonneg x y z t)
  rw [betaZNumerator, Complex.normSq_neg, Complex.normSq_mul, h4z, hbr]
  calc (16:ℝ) * (z * z) * (x * x + y * y)
      = 16 * (z * z * (x * x + y * y)) := by ring
    _ ≤ 16 * (majorantSum x y z t * majorantSum x y z t) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 72 * majorantSum x y z t ^ 2 := by
        nlinarith [sq_nonneg (majorantSum x y z t)]

/-- A two-sided Cauchy-type bound: a difference of products of complex numbers
with `K`- and `L`-majorized squared norms is majorized by
`2 (K L + K L)` fourth powers of the majorant. -/
theorem normSq_sub_prod_le {a b c d : ℂ} {K L S : ℝ} (hK : (0 : ℝ) ≤ K)
    (ha : Complex.normSq a ≤ K * S ^ 2) (hb : Complex.normSq b ≤ L * S ^ 2)
    (hc : Complex.normSq c ≤ K * S ^ 2) (hd : Complex.normSq d ≤ L * S ^ 2) :
    Complex.normSq (a * b - c * d) ≤ 2 * (K * L + K * L) * S ^ 4 := by
  have htri : Complex.normSq (a * b - c * d) ≤
      2 * (Complex.normSq (a * b) + Complex.normSq (c * d)) :=
    normSq_sub_le _ _
  have h1 : Complex.normSq (a * b) = Complex.normSq a * Complex.normSq b :=
    Complex.normSq_mul _ _
  have h2 : Complex.normSq (c * d) = Complex.normSq c * Complex.normSq d :=
    Complex.normSq_mul _ _
  have hKS : (0 : ℝ) ≤ K * S ^ 2 := mul_nonneg hK (sq_nonneg S)
  have hprod1 : Complex.normSq a * Complex.normSq b ≤ K * L * S ^ 4 := by
    have h := mul_le_mul ha hb (Complex.normSq_nonneg _) hKS
    have heq : (K * S ^ 2) * (L * S ^ 2) = K * L * S ^ 4 := by ring
    rwa [heq] at h
  have hprod2 : Complex.normSq c * Complex.normSq d ≤ K * L * S ^ 4 := by
    have h := mul_le_mul hc hd (Complex.normSq_nonneg _) hKS
    have heq : (K * S ^ 2) * (L * S ^ 2) = K * L * S ^ 4 := by ring
    rwa [heq] at h
  nlinarith [htri, h1, h2, hprod1, hprod2]

/-- Every entry of the cross-product numerator of the field is dominated by
`57600` fourth powers of the majorant. -/
theorem normSq_crossNumerators_le (x y z t : ℝ) (j : Fin 3) :
    Complex.normSq (cross3 (alphaGradientNumerators x y z t)
        (betaGradientNumerators x y z t) j) ≤
      57600 * majorantSum x y z t ^ 4 := by
  have eX0 := normSq_alphaXNumerator_le x y z t
  have eY0 := normSq_alphaYNumerator_le x y z t
  have eX : Complex.normSq (alphaXNumerator x y z t) ≤
      200 * majorantSum x y z t ^ 2 := by
    nlinarith [eX0, majorantSum_nonneg x y z t]
  have eY : Complex.normSq (alphaYNumerator x y z t) ≤
      200 * majorantSum x y z t ^ 2 := by
    nlinarith [eY0, majorantSum_nonneg x y z t]
  have eZ := normSq_alphaZNumerator_le x y z t
  have fX := normSq_betaXNumerator_le x y z t
  have fY := normSq_betaYNumerator_le x y z t
  have fZ := normSq_betaZNumerator_le x y z t
  have hnum : (2 : ℝ) * (200 * 72 + 200 * 72) * majorantSum x y z t ^ 4 =
      57600 * majorantSum x y z t ^ 4 := by norm_num
  fin_cases j
  · show Complex.normSq (alphaYNumerator x y z t * betaZNumerator x y z t -
        alphaZNumerator x y z t * betaYNumerator x y z t) ≤
      57600 * majorantSum x y z t ^ 4
    exact le_trans (normSq_sub_prod_le (by norm_num) eY fZ eZ fY)
      (le_of_eq hnum)
  · show Complex.normSq (alphaZNumerator x y z t * betaXNumerator x y z t -
        alphaXNumerator x y z t * betaZNumerator x y z t) ≤
      57600 * majorantSum x y z t ^ 4
    exact le_trans (normSq_sub_prod_le (by norm_num) eZ fX eX fZ)
      (le_of_eq hnum)
  · show Complex.normSq (alphaXNumerator x y z t * betaYNumerator x y z t -
        alphaYNumerator x y z t * betaXNumerator x y z t) ≤
      57600 * majorantSum x y z t ^ 4
    exact le_trans (normSq_sub_prod_le (by norm_num) eX fY eY fX)
      (le_of_eq hnum)

/-! ### Pointwise decay and the energy density -/

/-- The fourth power of the common denominator has squared modulus
`pairDenominator ^ 4`. -/
theorem normSq_complexDenominator_pow4 (x y z t : ℝ) :
    Complex.normSq (complexDenominator x y z t ^ 4) = pairDenominator x y z t ^ 4 := by
  have hp : complexDenominator x y z t ^ 4 =
      (complexDenominator x y z t * complexDenominator x y z t) *
      (complexDenominator x y z t * complexDenominator x y z t) := by ring
  rw [hp, Complex.normSq_mul, Complex.normSq_mul, normSq_complexDenominator]
  ring

/-- The majorant is dominated by the product of the spatial and temporal
radial factors. -/
theorem majorantSum_le_coords (x y z t : ℝ) :
    majorantSum x y z t ≤ (1 + x ^ 2 + y ^ 2 + z ^ 2) * (1 + t ^ 2) := by
  have h2 : (1 : ℝ) ≤ 1 + x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have h3 : t * t * 1 ≤ t * t * (1 + x ^ 2 + y ^ 2 + z ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by nlinarith [sq_nonneg t])
  simp only [majorantSum]
  linarith [h3]

/-- The fourth power of the majorant is dominated by the product of the
fourth powers of the radial factors. -/
theorem majorantSum_pow4_le (x y z t : ℝ) :
    majorantSum x y z t ^ 4 ≤
      (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4 * (1 + t ^ 2) ^ 4 := by
  have h := pow_le_pow_left₀ (majorantSum_nonneg x y z t)
    (majorantSum_le_coords x y z t) 4
  rwa [mul_pow] at h

/-- Fourth-power lower bound for the common denominator, in variables. -/
theorem denominator_pow8_lower {u v pd : ℝ} (h1 : u ^ 2 ≤ 4 * v ^ 2 * pd) :
    u ^ 8 ≤ 256 * v ^ 8 * pd ^ 4 := by
  have h2 : (u ^ 2) ^ 4 ≤ (4 * v ^ 2 * pd) ^ 4 :=
    pow_le_pow_left₀ (sq_nonneg u) h1 4
  calc u ^ 8 = (u ^ 2) ^ 4 := by ring
    _ ≤ (4 * v ^ 2 * pd) ^ 4 := h2
    _ = 256 * v ^ 8 * pd ^ 4 := by
        rw [mul_pow, mul_pow, ← pow_mul]
        norm_num

/-- Weighted fourth-power variant of the denominator lower bound. -/
theorem denominator_pow8_mul_lower {u v pd : ℝ} (hv4 : (0 : ℝ) ≤ v ^ 4)
    (h : u ^ 8 ≤ 256 * v ^ 8 * pd ^ 4) :
    u ^ 8 * v ^ 4 ≤ 256 * v ^ 12 * pd ^ 4 := by
  have h' := mul_le_mul_of_nonneg_right h hv4
  have heq : 256 * v ^ 8 * pd ^ 4 * v ^ 4 = 256 * v ^ 12 * pd ^ 4 := by ring
  rwa [heq] at h'

/-- Generic assembly of the decay estimate: from the cross-numerator
majorant, the majorant power bound, and the weighted denominator bound to
the final multiplication-form estimate. -/
theorem decay_assembly {A S u v pd : ℝ}
    (hu4 : (0 : ℝ) ≤ u ^ 4) (hc : A ≤ 57600 * S ^ 4)
    (hSpow : S ^ 4 ≤ u ^ 4 * v ^ 4)
    (hp8 : u ^ 8 * v ^ 4 ≤ 256 * v ^ 12 * pd) :
    A * u ^ 4 ≤ 14745600 * v ^ 12 * pd := by
  have hstep2 : 57600 * S ^ 4 ≤ 57600 * (u ^ 4 * v ^ 4) :=
    mul_le_mul_of_nonneg_left hSpow (by positivity)
  have hstep4 : 57600 * (u ^ 8 * v ^ 4) ≤ 57600 * (256 * v ^ 12 * pd) :=
    mul_le_mul_of_nonneg_left hp8 (by positivity)
  calc A * u ^ 4 ≤ 57600 * S ^ 4 * u ^ 4 :=
        mul_le_mul_of_nonneg_right hc hu4
    _ ≤ 57600 * (u ^ 4 * v ^ 4) * u ^ 4 :=
        mul_le_mul_of_nonneg_right hstep2 hu4
    _ = 57600 * (u ^ 8 * v ^ 4) := by ring
    _ ≤ 57600 * (256 * v ^ 12 * pd) := hstep4
    _ = 14745600 * v ^ 12 * pd := by ring

/-- The pointwise decay bound of the field: every entry of `F` is majorized by
`14745600 (1 + t²) ^ 12` over the fourth power of `1 + x² + y² + z²`. -/
theorem normSq_rationalField_le (x y z t : ℝ) (j : Fin 3) :
    Complex.normSq (rationalField x y z t j) ≤
      14745600 * (1 + t ^ 2) ^ 12 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4 := by
  set u : ℝ := 1 + x ^ 2 + y ^ 2 + z ^ 2 with hu
  set v : ℝ := 1 + t ^ 2 with hv
  have hu0 : (0 : ℝ) < u := by
    rw [hu]
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hv0 : (0 : ℝ) ≤ v := by
    rw [hv]
    positivity
  have hv4 : (0 : ℝ) ≤ v ^ 4 := pow_nonneg hv0 4
  have hu4 : (0 : ℝ) ≤ u ^ 4 := pow_nonneg (le_of_lt hu0) 4
  have h1 : u ^ 2 ≤ 4 * v ^ 2 * pairDenominator x y z t :=
    pairDenominator_lower x y z t
  have hp8 : u ^ 8 * v ^ 4 ≤ 256 * v ^ 12 * pairDenominator x y z t ^ 4 :=
    denominator_pow8_mul_lower hv4 (denominator_pow8_lower h1)
  have hSpow : majorantSum x y z t ^ 4 ≤ u ^ 4 * v ^ 4 := by
    have h := majorantSum_pow4_le x y z t
    rw [← hu, ← hv] at h
    exact h
  have hc := normSq_crossNumerators_le x y z t j
  rw [rationalField_eq_cross_div x y z t j, Complex.normSq_div,
    normSq_complexDenominator_pow4, le_div_iff₀ (pow_pos hu0 4),
    div_mul_eq_mul_div, div_le_iff₀ (pow_pos (pair_denominator_pos x y z t) 4)]
  exact decay_assembly hu4 hc hSpow hp8

/-- The energy density of the field, `∑ j ‖F j‖²`, equals the paper's
`|E|² + |B|²` with `E` and `B` the real and imaginary parts of `F`. -/
theorem rationalField_energy_density (x y z t : ℝ) :
    ∑ j : Fin 3, Complex.normSq (rationalField x y z t j) =
      dot3 (fun j => (rationalField x y z t j).re) (fun j => (rationalField x y z t j).re) +
      dot3 (fun j => (rationalField x y z t j).im) (fun j => (rationalField x y z t j).im) := by
  simp only [dot3, Fin.sum_univ_three, Complex.normSq_apply]
  ring
