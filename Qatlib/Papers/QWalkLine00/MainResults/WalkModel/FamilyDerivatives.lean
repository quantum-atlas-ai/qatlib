/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.StationaryAndFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives for the coin-angle dispersion family

For the dispersion family `dispersionTheta`, this module computes the first two derivative
expressions and evaluates them at `kAlphaTheta`. Interior assumptions on the coin angle and
scaled position ensure the required denominators are positive; the resulting identities support
the parameterized line-walk analysis of [NayakVishwanath2000].

## Main statements

* `hasDerivAt_dispersionTheta`: differentiates the parameterized dispersion relation.
* `dispersionTheta_second_at_kAlphaTheta`: identifies the stationary curvature expression.
* `mean_abs_alpha_theta`: evaluates a normalized integral of the derivative expression.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real MeasureTheory
open scoped Interval

noncomputable section

/-- The sine of `dispersionTheta θ k` is `√(1 - (cos (θ / 2) * cos k)²)`. -/
lemma sin_dispersionTheta (θ k : ℝ) :
    Real.sin (dispersionTheta θ k)
      = Real.sqrt (1 - (Real.cos (θ / 2) * Real.cos k) ^ 2) := by
  unfold dispersionTheta
  exact Real.sin_arccos _

/-- The sine of the parameterized dispersion is positive when `|cos (θ / 2) * cos k| < 1`. -/
lemma sin_dispersionTheta_pos {θ k : ℝ} (hk : |Real.cos (θ / 2) * Real.cos k| < 1) :
    0 < Real.sin (dispersionTheta θ k) := by
  rw [sin_dispersionTheta]
  apply Real.sqrt_pos.2
  have := abs_lt.mp hk
  nlinarith [this.1, this.2]

/-- For `0 < θ < π`, the square of `cos (θ / 2)` is strictly smaller than one. -/
lemma cos_half_sq_lt_one {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    Real.cos (θ / 2) ^ 2 < 1 := by
  have hlt : Real.cos (θ / 2) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ / 2)
      (le_refl (0 : ℝ)) (by linarith [Real.pi_pos]) (by linarith)
    simpa using this
  have hpos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  nlinarith

/-- When `|cos (θ / 2) * cos k| < 1`, the derivative of `dispersionTheta θ` at `k` is `sin k *
cos (θ / 2) / sin (dispersionTheta θ k)`. See [NayakVishwanath2000]. -/
theorem hasDerivAt_dispersionTheta {θ k : ℝ}
    (hk : |Real.cos (θ / 2) * Real.cos k| < 1) :
    HasDerivAt (fun x : ℝ => dispersionTheta θ x)
      (Real.sin k * Real.cos (θ / 2) / Real.sin (dispersionTheta θ k)) k := by
  have hmem := abs_lt.mp hk
  have hinner : HasDerivAt (fun x : ℝ => Real.cos (θ / 2) * Real.cos x)
      (Real.cos (θ / 2) * -Real.sin k) k :=
    (Real.hasDerivAt_cos k).const_mul (Real.cos (θ / 2))
  have houte := Real.hasDerivAt_arccos
    (x := Real.cos (θ / 2) * Real.cos k)
    (by intro h; linarith [hmem.1, h])
    (by intro h; linarith [hmem.2, h])
  have hcomp := houte.comp k hinner
  unfold dispersionTheta
  convert! hcomp using 1
  rw [Real.sin_arccos]
  field_simp

/-- Under the strict interior condition, the derivative of the first-derivative expression is
`cot (dispersionTheta θ k)` times one minus the square of that expression. See
[NayakVishwanath2000]. -/
theorem hasDerivAt_deriv_dispersionTheta {θ k : ℝ}
    (hk : |Real.cos (θ / 2) * Real.cos k| < 1) :
    HasDerivAt (fun x : ℝ => Real.sin x * Real.cos (θ / 2) / Real.sin (dispersionTheta θ x))
      (Real.cos (dispersionTheta θ k) / Real.sin (dispersionTheta θ k)
        * (1 - (Real.sin k * Real.cos (θ / 2) / Real.sin (dispersionTheta θ k)) ^ 2)) k := by
  have hsinpos : Real.sin (dispersionTheta θ k) ≠ 0 :=
    ne_of_gt (sin_dispersionTheta_pos hk)
  have hω := hasDerivAt_dispersionTheta (θ := θ) (k := k) hk
  have hg : HasDerivAt (fun x : ℝ => Real.sin (dispersionTheta θ x))
      (Real.cos (dispersionTheta θ k)
        * (Real.sin k * Real.cos (θ / 2) / Real.sin (dispersionTheta θ k))) k := by
    have := (Real.hasDerivAt_sin (dispersionTheta θ k)).comp k hω
    simpa using! this
  have hf : HasDerivAt (fun x : ℝ => Real.sin x * Real.cos (θ / 2))
      (Real.cos k * Real.cos (θ / 2)) k :=
    (Real.hasDerivAt_sin k).mul_const (Real.cos (θ / 2))
  have hq := hf.div hg hsinpos
  have hcos := cos_dispersionTheta θ k
  convert! hq using 1
  rw [hcos]
  field_simp

/-- For `0 < θ < π` and `α² < cos² (θ / 2)`, the sine of `kAlphaTheta θ α` equals `α / √(1 - α²)
* tan (θ / 2)`. See [NayakVishwanath2000]. -/
theorem sin_kAlphaTheta {θ α : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    Real.sin (kAlphaTheta θ α)
      = α / Real.sqrt (1 - α ^ 2) * Real.tan (θ / 2) := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hα1 : α ^ 2 < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hcos0 : Real.cos (θ / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

  have htan : Real.cos (θ / 2) ^ 2 * (1 + Real.tan (θ / 2) ^ 2) = 1 := by
    have := Real.inv_one_add_tan_sq hcos0
    field_simp at this ⊢
    linarith [this]

  have harg : |α / Real.sqrt (1 - α ^ 2) * Real.tan (θ / 2)| < 1 := by
    have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt h1.le
    have htan2 : Real.tan (θ / 2) ^ 2 * Real.cos (θ / 2) ^ 2 = 1 - Real.cos (θ / 2) ^ 2 := by
      nlinarith [htan]
    rw [abs_mul, abs_div, abs_of_pos (Real.sqrt_pos.2 h1), abs_of_pos
      (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith))]
    rw [div_mul_eq_mul_div, div_lt_one (Real.sqrt_pos.2 h1)]

    have habsα : |α| ^ 2 = α ^ 2 := sq_abs α
    have htan2' : Real.tan (θ / 2) ^ 2 = (1 - Real.cos (θ / 2) ^ 2) / Real.cos (θ / 2) ^ 2 := by
      field_simp
      linarith [htan]
    have hleft : (|α| * Real.tan (θ / 2)) ^ 2
        = α ^ 2 * (1 - Real.cos (θ / 2) ^ 2) / Real.cos (θ / 2) ^ 2 := by
      rw [mul_pow, habsα, htan2']; ring
    have hright : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := hsq
    have hnonneg : (0 : ℝ) ≤ |α| * Real.tan (θ / 2) :=
      mul_nonneg (abs_nonneg α)
        (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)).le
    have hL : (|α| * Real.tan (θ / 2)) ^ 2 < (Real.sqrt (1 - α ^ 2)) ^ 2 := by
      rw [hleft, hright]
      have hcpos2 : 0 < Real.cos (θ / 2) ^ 2 := by positivity
      rw [div_lt_iff₀ hcpos2]
      nlinarith [hα]
    nlinarith [hL, hnonneg, Real.sqrt_pos.2 h1, sq_nonneg (|α| * Real.tan (θ / 2))]
  rw [kAlphaTheta]
  rw [Real.sin_arcsin (le_of_lt (abs_lt.mp harg).1) (le_of_lt (abs_lt.mp harg).2)]

/-- In the interior regime, `cos² (kAlphaTheta θ α)` equals `(cos² (θ / 2) - α²) / (cos² (θ / 2)
* (1 - α²))`. -/
theorem cos_sq_kAlphaTheta {θ α : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    Real.cos (kAlphaTheta θ α) ^ 2
      = (Real.cos (θ / 2) ^ 2 - α ^ 2) / (Real.cos (θ / 2) ^ 2 * (1 - α ^ 2)) := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hα1 : α ^ 2 < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hcos0 : Real.cos (θ / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hsin := sin_kAlphaTheta hθ0 hθπ hα
  have htrig := Real.sin_sq_add_cos_sq (kAlphaTheta θ α)
  have htan : Real.cos (θ / 2) ^ 2 * (1 + Real.tan (θ / 2) ^ 2) = 1 := by
    have := Real.inv_one_add_tan_sq hcos0
    field_simp at this ⊢
    linarith [this]
  have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt h1.le
  have hsin2 : Real.sin (kAlphaTheta θ α) ^ 2
      = α ^ 2 * Real.tan (θ / 2) ^ 2 / (1 - α ^ 2) := by
    rw [hsin]
    field_simp
    rw [hsq]
  have htan2 : Real.tan (θ / 2) ^ 2 = (1 - Real.cos (θ / 2) ^ 2) / Real.cos (θ / 2) ^ 2 := by
    field_simp
    linarith [htan]
  have hcos2' : Real.cos (kAlphaTheta θ α) ^ 2
      = 1 - Real.sin (kAlphaTheta θ α) ^ 2 := by linarith [htrig]
  rw [hcos2', hsin2, htan2]
  field_simp
  ring

/-- In the interior regime, the squared sine of the dispersion at `kAlphaTheta θ α` equals `sin²
(θ / 2) / (1 - α²)`. -/
theorem sin_sq_dispersionTheta_at_kAlpha {θ α : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    Real.sin (dispersionTheta θ (kAlphaTheta θ α)) ^ 2
      = Real.sin (θ / 2) ^ 2 / (1 - α ^ 2) := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hα1 : α ^ 2 < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hcos0 : Real.cos (θ / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [sin_dispersionTheta]
  have hcos := cos_sq_kAlphaTheta hθ0 hθπ hα
  have htrig := Real.sin_sq_add_cos_sq (θ / 2)
  have hsq : (Real.sqrt (1 - (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)) ^ 2)) ^ 2
      = 1 - (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)) ^ 2 := by
    apply Real.sq_sqrt
    have h2' : |Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)| ≤ 1 := by
      rw [abs_mul]
      nlinarith [Real.abs_cos_le_one (θ / 2), Real.abs_cos_le_one (kAlphaTheta θ α),
        abs_nonneg (Real.cos (θ / 2)), abs_nonneg (Real.cos (kAlphaTheta θ α))]
    nlinarith [sq_abs (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)), h2',
      abs_nonneg (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α))]
  rw [hsq]
  have hkey : (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)) ^ 2
      = (Real.cos (θ / 2) ^ 2 - α ^ 2) / (1 - α ^ 2) := by
    rw [mul_pow, hcos]
    field_simp
  rw [hkey]
  have htrig2 : Real.sin (θ / 2) ^ 2 = 1 - Real.cos (θ / 2) ^ 2 := by linarith [htrig]
  rw [htrig2]
  field_simp
  ring

/-- In the interior regime, the first-derivative expression for `dispersionTheta θ` evaluated at
`kAlphaTheta θ α` equals `α`. -/
theorem dispersionTheta_deriv_at_kAlphaTheta {θ α : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    Real.sin (kAlphaTheta θ α) * Real.cos (θ / 2)
        / Real.sin (dispersionTheta θ (kAlphaTheta θ α)) = α := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hα1 : α ^ 2 < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hcos0 : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsin0 : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin := sin_kAlphaTheta hθ0 hθπ hα
  have hsinω_sq := sin_sq_dispersionTheta_at_kAlpha hθ0 hθπ hα
  have hsinω_pos : 0 < Real.sin (dispersionTheta θ (kAlphaTheta θ α)) := by
    rw [sin_dispersionTheta]
    apply Real.sqrt_pos.2
    have hclt : |Real.cos (θ / 2)| < 1 := by
      rw [abs_of_pos hcos0]
      nlinarith [hc2]
    have hcle : |Real.cos (kAlphaTheta θ α)| ≤ 1 := Real.abs_cos_le_one _
    have hX : |Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)| < 1 := by
      rw [abs_mul]
      nlinarith [hclt, hcle, abs_nonneg (Real.cos (θ / 2)),
        abs_nonneg (Real.cos (kAlphaTheta θ α))]
    have hs := sq_abs (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α))
    nlinarith [hX, abs_nonneg (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α))]
  have hsinω : Real.sin (dispersionTheta θ (kAlphaTheta θ α))
      = Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2) := by
    have h2 : (Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2)) ^ 2 = Real.sin (θ / 2) ^ 2 / (1 - α ^ 2) := by
      rw [div_pow, Real.sq_sqrt h1.le]
    have hpos2 : 0 ≤ Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2) :=
      div_nonneg hsin0.le (Real.sqrt_pos.2 h1).le
    have := hsinω_sq
    rw [← h2] at this
    exact (sq_eq_sq₀ hsinω_pos.le hpos2).mp this
  rw [hsin, hsinω]
  have htan : Real.tan (θ / 2) = Real.sin (θ / 2) / Real.cos (θ / 2) := Real.tan_eq_sin_div_cos _
  rw [htan]
  field_simp

/-- In the interior regime, the second-derivative expression at `kAlphaTheta θ α` equals
`omegaSecondAtStationaryTheta θ α`. See [NayakVishwanath2000]. -/
theorem dispersionTheta_second_at_kAlphaTheta {θ α : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    Real.cos (dispersionTheta θ (kAlphaTheta θ α))
        / Real.sin (dispersionTheta θ (kAlphaTheta θ α))
        * (1 - (Real.sin (kAlphaTheta θ α) * Real.cos (θ / 2)
            / Real.sin (dispersionTheta θ (kAlphaTheta θ α))) ^ 2)
      = omegaSecondAtStationaryTheta θ α := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hα1 : α ^ 2 < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hcos0 : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsin0 : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsinω_pos : 0 < Real.sin (dispersionTheta θ (kAlphaTheta θ α)) := by
    rw [sin_dispersionTheta]
    apply Real.sqrt_pos.2
    have hclt : |Real.cos (θ / 2)| < 1 := by
      rw [abs_of_pos hcos0]
      nlinarith [hc2]
    have hcle : |Real.cos (kAlphaTheta θ α)| ≤ 1 := Real.abs_cos_le_one _
    have hX : |Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α)| < 1 := by
      rw [abs_mul]
      nlinarith [hclt, hcle, abs_nonneg (Real.cos (θ / 2)),
        abs_nonneg (Real.cos (kAlphaTheta θ α))]
    have hs := sq_abs (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α))
    nlinarith [hX, abs_nonneg (Real.cos (θ / 2) * Real.cos (kAlphaTheta θ α))]
  have hsinω : Real.sin (dispersionTheta θ (kAlphaTheta θ α))
      = Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2) := by
    have hsinω_sq := sin_sq_dispersionTheta_at_kAlpha hθ0 hθπ hα
    have h2 : (Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2)) ^ 2 = Real.sin (θ / 2) ^ 2 / (1 - α ^ 2) := by
      rw [div_pow, Real.sq_sqrt h1.le]
    have hpos2 : 0 ≤ Real.sin (θ / 2) / Real.sqrt (1 - α ^ 2) :=
      div_nonneg hsin0.le (Real.sqrt_pos.2 h1).le
    rw [← h2] at hsinω_sq
    exact (sq_eq_sq₀ hsinω_pos.le hpos2).mp hsinω_sq
  have hcos2 : Real.cos (dispersionTheta θ (kAlphaTheta θ α)) ^ 2
      = (Real.cos (θ / 2) ^ 2 - α ^ 2) / (1 - α ^ 2) := by
    rw [cos_dispersionTheta, mul_pow, cos_sq_kAlphaTheta hθ0 hθπ hα]
    field_simp
  have hcosω_nonneg : 0 ≤ Real.cos (dispersionTheta θ (kAlphaTheta θ α)) := by
    rw [cos_dispersionTheta]
    refine mul_nonneg hcos0.le ?_
    rw [kAlphaTheta, Real.cos_arcsin]
    exact Real.sqrt_nonneg _
  have hcosω : Real.cos (dispersionTheta θ (kAlphaTheta θ α))
      = Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) / Real.sqrt (1 - α ^ 2) := by
    have hd : 0 ≤ Real.cos (θ / 2) ^ 2 - α ^ 2 := by linarith [hα]
    have h2 : (Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) / Real.sqrt (1 - α ^ 2)) ^ 2
        = (Real.cos (θ / 2) ^ 2 - α ^ 2) / (1 - α ^ 2) := by
      rw [div_pow, Real.sq_sqrt hd, Real.sq_sqrt h1.le]
    have hpos2 : 0 ≤ Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) / Real.sqrt (1 - α ^ 2) :=
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_pos.2 h1).le
    have h := hcos2
    rw [← h2] at h
    exact (sq_eq_sq₀ hcosω_nonneg hpos2).mp h
  have hderiv := dispersionTheta_deriv_at_kAlphaTheta hθ0 hθπ hα
  have hsqrtpos : 0 < Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) :=
    Real.sqrt_pos.2 (by linarith [hα])
  rw [hderiv]
  rw [hcosω, hsinω]
  unfold omegaSecondAtStationaryTheta
  field_simp

/-- For `0 < θ < π`, the quantity `|cos (θ / 2) * cos k|` is strictly smaller than one for every
real `k`. -/
lemma cos_half_mul_cos_lt_one {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (k : ℝ) :
    |Real.cos (θ / 2) * Real.cos k| < 1 := by
  have hc2 : Real.cos (θ / 2) ^ 2 < 1 := cos_half_sq_lt_one hθ0 hθπ
  have hc0 : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc1 : Real.cos (θ / 2) < 1 := by nlinarith
  rw [abs_mul]
  rw [abs_of_pos hc0]
  have hck : |Real.cos k| ≤ 1 := Real.abs_cos_le_one k
  have hck0 : 0 ≤ |Real.cos k| := abs_nonneg _
  nlinarith

/-- For `0 < θ < π`, integrating the dispersion derivative expression over `[0, π / 2]` gives `π
/ 2 - θ / 2`. See [NayakVishwanath2000]. -/
theorem integral_dispersionTheta_deriv {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (∫ k in (0 : ℝ)..(Real.pi / 2),
        Real.sin k * Real.cos (θ / 2) / Real.sin (dispersionTheta θ k))
      = Real.pi / 2 - θ / 2 := by
  have hcontω : Continuous (fun x : ℝ => dispersionTheta θ x) := by
    unfold dispersionTheta
    exact Real.continuous_arccos.comp (by fun_prop)
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun x : ℝ => dispersionTheta θ x)
        (Real.sin x * Real.cos (θ / 2) / Real.sin (dispersionTheta θ x)) x := by
    intro x _
    exact hasDerivAt_dispersionTheta (cos_half_mul_cos_lt_one hθ0 hθπ x)
  have hne : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      Real.sin (dispersionTheta θ x) ≠ 0 := by
    intro x _
    exact ne_of_gt (sin_dispersionTheta_pos (cos_half_mul_cos_lt_one hθ0 hθπ x))
  have hcont' : ContinuousOn
      (fun x : ℝ => Real.sin x * Real.cos (θ / 2) / Real.sin (dispersionTheta θ x))
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    apply ContinuousOn.div
    · exact (by fun_prop : Continuous fun x : ℝ => Real.sin x * Real.cos (θ / 2)).continuousOn
    · exact (Real.continuous_sin.comp hcontω).continuousOn
    · exact hne
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff hcont'.intervalIntegrable
  rw [h]
  have h1 : dispersionTheta θ (Real.pi / 2) = Real.pi / 2 := by
    unfold dispersionTheta
    rw [Real.cos_pi_div_two, mul_zero, Real.arccos_zero]
  have h2 : dispersionTheta θ 0 = θ / 2 := by
    unfold dispersionTheta
    rw [Real.cos_zero, mul_one]
    exact Real.arccos_cos (by linarith) (by linarith)
  rw [h1, h2]

/-- For `0 < θ < π`, the integral of the dispersion derivative expression over `[0, π / 2]`,
multiplied by `2 / π`, equals `1 - θ / π`. -/
theorem mean_abs_alpha_theta {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (2 / Real.pi) * ∫ k in (0 : ℝ)..(Real.pi / 2),
        Real.sin k * Real.cos (θ / 2) / Real.sin (dispersionTheta θ k)
      = 1 - θ / Real.pi := by
  rw [integral_dispersionTheta_deriv hθ0 hθπ]
  field_simp

end

end Qatlib.Papers.QWalkLine00.MainResults
