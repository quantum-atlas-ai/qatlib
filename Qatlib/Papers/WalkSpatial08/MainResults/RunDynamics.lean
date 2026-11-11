/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.SearchDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Two-mode rotation and target overlap

This module develops a finite complex inner product and squared norm for two-mode walk dynamics.
It defines a phase-evolving difference of two vectors and proves its normalization for
orthonormal modes, together with a sinusoidal target-overlap identity when the target overlaps
both modes equally.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `rotState_nrm2`: normalization of the rotating state.
* `rotState_bornProb`: exact sinusoidal overlap formula.
* `rotState_success_ge`: a lower bound from the overlap and rotation angle.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.WalkSpatial08.MainResults

variable {ι : Type*} [Fintype ι]

/-- The finite complex inner product, conjugate-linear in the first argument and linear in the
second. -/
def ip (f g : ι → ℂ) : ℂ := ∑ i, conj (f i) * g i

/-- The squared Euclidean norm of a finite complex vector, expressed as a sum of squared
amplitude norms. -/
def nrm2 (f : ι → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2

/-- The squared norm `nrm2` is nonnegative. -/
theorem nrm2_nonneg (f : ι → ℂ) : 0 ≤ nrm2 f := by
  unfold nrm2
  exact Finset.sum_nonneg (fun i _ => by positivity)

/-- The inner product of a vector with itself is its squared norm embedded in the complex
numbers. -/
theorem ip_self (f : ι → ℂ) : ip f f = (nrm2 f : ℂ) := by
  unfold ip nrm2
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Complex.conj_mul' (f i)

/-- The real part of the finite inner product is the sum of the real parts of its coordinate
terms. -/
theorem ip_re (f g : ι → ℂ) : (ip f g).re = ∑ i, (conj (f i) * g i).re := by
  unfold ip
  exact Complex.re_sum Finset.univ _

/-- The inner product distributes over subtraction in its second argument. -/
theorem ip_sub_right (f g h : ι → ℂ) :
    ip f (fun i => g i - h i) = ip f g - ip f h := by
  unfold ip
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Scaling the second vector multiplies the inner product by the same complex scalar. -/
theorem ip_smul_right (f g : ι → ℂ) (c : ℂ) :
    ip f (fun i => c * g i) = c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The inner product distributes over addition in its second argument. -/
theorem ip_add_right (f g h : ι → ℂ) :
    ip f (fun i => g i + h i) = ip f g + ip f h := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Scaling the first vector multiplies the inner product by the conjugate scalar. -/
theorem ip_smul_left (f g : ι → ℂ) (c : ℂ) :
    ip (fun i => c * f i) g = conj c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [map_mul]
  ring

/-- Complex scalar multiplication scales the squared norm by the squared scalar norm. -/
theorem nrm2_smul (f : ι → ℂ) (c : ℂ) :
    nrm2 (fun i => c * f i) = ‖c‖ ^ 2 * nrm2 f := by
  unfold nrm2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [norm_mul, mul_pow]

/-- The complex phase `exp (I * θ)` has norm one for real `θ`. -/
theorem norm_exp_I_mul (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (θ : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- The squared norm of the difference of orthogonal vectors is the sum of their squared norms. -/
theorem nrm2_sub_of_orthogonal (f g : ι → ℂ) (h : ip f g = 0) :
    nrm2 (fun i => f i - g i) = nrm2 f + nrm2 g := by
  have hre : ∑ i, (conj (f i) * g i).re = 0 := by
    rw [← ip_re, h]; simp
  have hterm : ∀ i : ι, ‖f i - g i‖ ^ 2
      = ‖f i‖ ^ 2 + ‖g i‖ ^ 2 - 2 * ((conj (f i) * g i).re) := by
    intro i
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    congr 1
    congr 1

    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [nrm2]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hre]
  ring

/-- The difference of `u` and `v` with opposite phases `exp (±I * T * α)`, scaled by the inverse
square root of two. -/
def rotState (α : ℝ) (T : ℕ) (u v : ι → ℂ) : ι → ℂ :=
  fun i => ((Real.sqrt 2 : ℂ))⁻¹ *
    (Complex.exp (Complex.I * (((T : ℝ) * α : ℝ) : ℂ)) * u i
      - Complex.exp (-(Complex.I * (((T : ℝ) * α : ℝ) : ℂ))) * v i)

/-- The sum of two vectors scaled by the inverse square root of two. -/
def alphaPlus (u v : ι → ℂ) : ι → ℂ :=
  fun i => ((Real.sqrt 2 : ℂ))⁻¹ * (u i + v i)

/-- The squared norm of the inner product of a target vector with a state vector. -/
def bornProb (t ψ : ι → ℂ) : ℝ := ‖ip t ψ‖ ^ 2

/-- The complex inverse of `sqrt 2` has norm equal to the real inverse of `sqrt 2`. -/
theorem norm_sqrt2_inv : ‖((Real.sqrt 2 : ℂ))⁻¹‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The norm of `2 * I * sin θ` equals `2 * |sin θ|`. -/
theorem norm_two_I_sin (θ : ℝ) :
    ‖(2 : ℂ) * Complex.I * (Real.sin θ : ℂ)‖ = 2 * |Real.sin θ| := by
  rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- For orthogonal unit vectors `u` and `v`, the rotating state has squared norm one. -/
theorem rotState_nrm2 (α : ℝ) (T : ℕ) {u v : ι → ℂ}
    (hu : nrm2 u = 1) (hv : nrm2 v = 1) (huv : ip u v = 0) :
    nrm2 (rotState α T u v) = 1 := by
  set θ : ℝ := (T : ℝ) * α with hθ
  set a : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with ha
  set b : ℂ := Complex.exp (-(Complex.I * (θ : ℂ))) with hb
  have han : ‖a‖ = 1 := norm_exp_I_mul θ
  have hbn : ‖b‖ = 1 := by
    rw [hb]
    have hcast : -(Complex.I * (θ : ℂ)) = Complex.I * ((-θ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact norm_exp_I_mul (-θ)
  have horth : ip (fun i => a * u i) (fun i => b * v i) = 0 := by
    rw [ip_smul_left, ip_smul_right, huv]
    ring
  have hsplit : rotState α T u v
      = (fun i => ((Real.sqrt 2 : ℂ))⁻¹ * (a * u i - b * v i)) := by
    funext i
    rw [rotState]
  rw [hsplit, nrm2_smul]
  have hpy : nrm2 (fun i => a * u i - b * v i)
      = nrm2 (fun i => a * u i) + nrm2 (fun i => b * v i) :=
    nrm2_sub_of_orthogonal _ _ horth
  rw [hpy, nrm2_smul, nrm2_smul, han, hbn, hu, hv]
  have hsqrt : ‖((Real.sqrt 2 : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_sqrt2_inv, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hsqrt]
  norm_num

/-- If the target has equal inner products with both modes, its overlap square with the rotating
state equals its overlap square with `alphaPlus` times `sin (T * α)²`. See [Main result:
O(sqrt(N log N)) two-dimensional spatial search][Tulsi2008]. -/
theorem rotState_bornProb (α : ℝ) (T : ℕ) {t u v : ι → ℂ}
    (ha : ip t u = ip t v) :
    bornProb t (rotState α T u v)
      = bornProb t (alphaPlus u v) * Real.sin (((T : ℝ) * α)) ^ 2 := by
  set θ : ℝ := (T : ℝ) * α with hθ
  set a : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with ha'
  set b : ℂ := Complex.exp (-(Complex.I * (θ : ℂ))) with hb'
  set a0 : ℂ := ip t u with ha0
  have hvt : ip t v = a0 := ha.symm
  have hdiff : a - b = 2 * Complex.I * (Real.sin θ : ℂ) := by
    rw [ha', hb']
    have h1 : Complex.exp (Complex.I * (θ : ℂ))
        = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
      rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    have h2 : Complex.exp (-(Complex.I * (θ : ℂ)))
        = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
      rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_neg,
        Complex.cos_neg, Complex.sin_neg]
      ring
    rw [h1, h2]; ring
  have hips : ip t (rotState α T u v) = ((Real.sqrt 2 : ℂ))⁻¹ * ((a - b) * a0) := by
    have hfun : rotState α T u v
        = (fun i => ((Real.sqrt 2 : ℂ))⁻¹ * (a * u i - b * v i)) := by
      funext i; simp only [rotState, hθ, ha', hb']
    have hau : ip t (fun i => a * u i) = a * a0 := by
      rw [ip_smul_right, ha0]
    have hbv : ip t (fun i => b * v i) = b * a0 := by
      rw [ip_smul_right, hvt]
    rw [hfun, ip_smul_right, ip_sub_right, hau, hbv]
    ring
  have hplus : bornProb t (alphaPlus u v) = 2 * ‖a0‖ ^ 2 := by
    have hfun : alphaPlus u v = (fun i => ((Real.sqrt 2 : ℂ))⁻¹ * (u i + v i)) := by
      funext i; rw [alphaPlus]
    unfold bornProb
    rw [hfun, ip_smul_right, ip_add_right, ← ha0, hvt, show a0 + a0 = 2 * a0 by ring]
    rw [norm_mul, norm_mul, norm_sqrt2_inv, Complex.norm_ofNat]
    rw [show ((Real.sqrt 2)⁻¹ * (2 * ‖a0‖)) ^ 2 = (Real.sqrt 2)⁻¹ ^ 2 * (2 * ‖a0‖) ^ 2 by ring,
      inv_pow, Real.sq_sqrt (by norm_num)]
    field_simp
  unfold bornProb
  rw [hips, hdiff]
  have hnorm : ‖((Real.sqrt 2 : ℂ))⁻¹ * (((2 : ℂ) * Complex.I * (Real.sin θ : ℂ)) * a0)‖
      = (Real.sqrt 2)⁻¹ * (2 * |Real.sin θ|) * ‖a0‖ := by
    rw [norm_mul, norm_sqrt2_inv, norm_mul, norm_two_I_sin]
    ring
  rw [hnorm, show ‖ip t (alphaPlus u v)‖ ^ 2 = 2 * ‖a0‖ ^ 2 from hplus]
  have h2' : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsin : |Real.sin θ| ^ 2 = Real.sin θ ^ 2 := sq_abs _
  rw [mul_pow, mul_pow, mul_pow, inv_pow, h2', hsin]
  field_simp

/-- The squared sine is at least one half for angles between `π / 4` and `π / 2`. -/
theorem sin_sq_ge_half {θ : ℝ} (h1 : Real.pi / 4 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    1 / 2 ≤ Real.sin θ ^ 2 := by
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 4) h2 h1
  have hval : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  rw [hval] at hmono
  have hpos : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hsq : (Real.sqrt 2 / 2) ^ 2 ≤ Real.sin θ ^ 2 :=
    pow_le_pow_left₀ hpos hmono 2
  have hsqval : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h2' : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h2']; norm_num
  linarith [hsqval, hsq]

/-- Equal target overlaps, an `alphaPlus` overlap lower bound `d2`, and a squared sine at least
one half give rotating-state overlap square at least `d2 / 2`. -/
theorem rotState_success_ge (α : ℝ) (T : ℕ) {t u v : ι → ℂ}
    (ha : ip t u = ip t v) {d2 : ℝ}
    (hle : d2 ≤ bornProb t (alphaPlus u v))
    (hs : 1 / 2 ≤ Real.sin (((T : ℝ) * α)) ^ 2) :
    d2 / 2 ≤ bornProb t (rotState α T u v) := by
  rw [rotState_bornProb α T ha]
  have hb : 0 ≤ bornProb t (alphaPlus u v) := by unfold bornProb; positivity
  have hmul := mul_le_mul hle hs (by norm_num : (0:ℝ) ≤ 1 / 2) hb
  linarith [hmul]

end Qatlib.Papers.WalkSpatial08.MainResults
