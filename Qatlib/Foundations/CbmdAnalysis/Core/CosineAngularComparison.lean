/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.PropagatorAngularGrowth
import Qatlib.Foundations.CbmdAnalysis.Core.CosinePropagators
import Qatlib.Foundations.CbmdAnalysis.Core.CosineCircleDenominator
import Qatlib.Foundations.CbmdAnalysis.Core.CosineCircleLimit

/-!
# Angular comparison with the cosine regulator

This module compares the angular growth bounds for wave, Bessel, and Airy matrix numerators with
the cosine regulator on expanding circles. The constant `cosineAngularConstant` absorbs the
contribution of `L`; positive definiteness of `H` and the bound `‖H‖ ≤ γ` yield the eventual
circle comparisons needed for [WangEtAl2026].

## Main statements

* `cosine_angular_exp_le`: bounds the wave angular exponential by the regulator norm.
* `waveCosineNumerator_circle_comparison`: eventual circle comparison for the wave numerator.
* `airyCosineNumerator_circle_comparison`: the corresponding Airy comparison after the Airy time
  change.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex Metric Set Filter
open scoped Topology Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive comparison constant `4 * exp 1 * exp (τ * ‖Ring.inverse (CFC.sqrt H) * L‖)` for
cosine contour estimates. -/
def cosineAngularConstant (L H : Matrix n n ℂ) (τ : ℝ) : ℝ :=
  4 * Real.exp 1 * Real.exp (τ * ‖Ring.inverse (CFC.sqrt H) * L‖)

/-- The cosine angular comparison constant is strictly positive for every `L`, `H`, and real
`τ`. -/
theorem cosineAngularConstant_pos (L H : Matrix n n ℂ) (τ : ℝ) :
    0 < cosineAngularConstant L H τ := by unfold cosineAngularConstant; positivity

/-- If the cosine circle radius is at least one, the norm of `sqrt (I * z)` is at least one at
every point on that circle. -/
private theorem circle_root_norm_ge_one {γ τ : ℝ} {N : ℕ}
    (hR : 1 ≤ cosineCircleRadius γ τ N) {z : ℂ}
    (hz : ‖z‖ = cosineCircleRadius γ τ N) : 1 ≤ ‖Complex.sqrt (I * z)‖ := by
  have hs : Complex.sqrt (I * z) ^ 2 = I * z := Complex.cpow_ofNat_inv_pow _ 2
  have hn := congrArg norm hs
  rw [norm_pow, norm_mul, norm_I, one_mul, hz] at hn
  nlinarith [norm_nonneg (Complex.sqrt (I * z))]

/-- If the cosine circle radius is at least one, `sqrt (I * z)` is nonzero at every point on
that circle. -/
private theorem circle_root_ne_zero {γ τ : ℝ} {N : ℕ}
    (hR : 1 ≤ cosineCircleRadius γ τ N) {z : ℂ}
    (hz : ‖z‖ = cosineCircleRadius γ τ N) : Complex.sqrt (I * z) ≠ 0 := by
  have h := circle_root_norm_ge_one hR hz
  intro he
  rw [he, norm_zero] at h
  norm_num at h

/-- For positive `γ` and `τ`, `‖H‖ ≤ γ`, and an index and circle radius at least one, the wave
angular exponential is bounded by `cosineAngularConstant L H τ` times the regulator norm. -/
theorem cosine_angular_exp_le (L H : Matrix n n ℂ) {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hγH : ‖H‖ ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (hR : 1 ≤ cosineCircleRadius γ τ N) (z : ℂ)
    (hz : ‖z‖ = cosineCircleRadius γ τ N) :
    Real.exp (τ * waveAngularRate L H (Complex.sqrt (I * z))) ≤
      cosineAngularConstant L H τ * ‖cosineRegulator γ τ z‖ := by
  let r := Complex.sqrt (I * z)
  let q : ℂ := ((τ * Real.sqrt γ : ℝ) : ℂ) * r
  have hrsq : r ^ 2 = I * z := Complex.cpow_ofNat_inv_pow _ 2
  have hq : q ^ 2 = I * (γ : ℂ) * (τ : ℂ) ^ 2 * z := by
    dsimp only [q]
    rw [mul_pow, ← Complex.ofReal_pow, mul_pow, Real.sq_sqrt hγ.le, hrsq]
    push_cast
    ring
  have hqim : |q.im| = τ * Real.sqrt γ * |r.im| := by
    simp only [q, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, abs_mul, abs_of_nonneg (mul_nonneg hτ.le (Real.sqrt_nonneg γ))]
  have hi : ‖r‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (circle_root_norm_ge_one hR hz)
  have hfirst := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hγH) (abs_nonneg r.im)
  have hsecond := mul_le_mul_of_nonneg_right hi (norm_nonneg (Ring.inverse (CFC.sqrt H) * L))
  have he : τ * waveAngularRate L H r ≤ |q.im| + τ * ‖Ring.inverse (CFC.sqrt H) * L‖ := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hτ.le
    rw [hqim]
    dsimp only [waveAngularRate]
    nlinarith
  have hden := (div_le_iff₀ (by positivity : 0 < 4 * Real.exp 1)).mp
    (cosineRegulator_circle_norm_lower_of_sq hγ hτ hN hz hq)
  calc
    _ ≤ Real.exp (|q.im| + τ * ‖Ring.inverse (CFC.sqrt H) * L‖) := Real.exp_le_exp.mpr he
    _ = Real.exp |q.im| * Real.exp (τ * ‖Ring.inverse (CFC.sqrt H) * L‖) := Real.exp_add _ _
    _ ≤ (‖cosineRegulator γ τ z‖ * (4 * Real.exp 1)) *
        Real.exp (τ * ‖Ring.inverse (CFC.sqrt H) * L‖) :=
      mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le
    _ = _ := by unfold cosineAngularConstant; ring

/-- For positive definite `H`, positive `γ` and `τ`, and `‖H‖ ≤ γ`, the wave numerator on all
sufficiently large cosine circles is bounded by the angular constant times the regulator
norm. -/
theorem waveCosineNumerator_circle_comparison (L H : Matrix n n ℂ) (hH : H.PosDef)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hγH : ‖H‖ ≤ γ) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (cosineCircleRadius γ τ N),
      ‖waveCosineNumerator L H (τ : ℂ) z‖ ≤
        cosineAngularConstant L H τ * ‖cosineRegulator γ τ z‖ := by
  filter_upwards [(cosineCircleRadius_tendsto hγ hτ).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with N hR hN
  intro z hz
  have hzn : ‖z‖ = cosineCircleRadius γ τ N := by
    simpa only [mem_sphere_iff_norm, sub_zero] using! hz
  have h := wavePropagator_matrix_angular L H hH (Complex.sqrt (I * z))
    (circle_root_ne_zero hR hzn) τ hτ.le
  have hs : Complex.sqrt (I * z) ^ 2 = I * z := Complex.cpow_ofNat_inv_pow _ 2
  rw [hs] at h
  exact h.trans (cosine_angular_exp_le L H hγ hτ hγH N hN hR z hzn)

/-- For positive definite `H`, positive `γ` and `τ`, and `‖H‖ ≤ γ`, the Bessel numerator on all
sufficiently large cosine circles is bounded by the angular constant times the regulator
norm. -/
theorem besselCosineNumerator_circle_comparison (L H : Matrix n n ℂ) (hH : H.PosDef)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hγH : ‖H‖ ≤ γ) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (cosineCircleRadius γ τ N),
      ‖besselCosineNumerator L H (τ : ℂ) z‖ ≤
        cosineAngularConstant L H τ * ‖cosineRegulator γ τ z‖ := by
  filter_upwards [(cosineCircleRadius_tendsto hγ hτ).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with N hR hN
  intro z hz
  have hzn : ‖z‖ = cosineCircleRadius γ τ N := by
    simpa only [mem_sphere_iff_norm, sub_zero] using! hz
  have h := besselPropagator_matrix_angular L H hH (Complex.sqrt (I * z))
    (circle_root_ne_zero hR hzn) τ hτ.le
  have hs : Complex.sqrt (I * z) ^ 2 = I * z := Complex.cpow_ofNat_inv_pow _ 2
  rw [hs] at h
  exact h.trans (cosine_angular_exp_le L H hγ hτ hγH N hN hR z hzn)

/-- The Airy time scale is strictly positive at every positive real time. -/
theorem airyTimeScale_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < airyTimeScale t := by
  unfold airyTimeScale
  positivity

/-- For positive definite `H`, positive `γ` and time, and `‖H‖ ≤ γ`, the Airy numerator is
eventually bounded on the cosine circles by the regulator norm times the angular constant
evaluated at `airyTimeScale t`. -/
theorem airyCosineNumerator_circle_comparison (L H : Matrix n n ℂ) (hH : H.PosDef)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hγH : ‖H‖ ≤ γ) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (cosineCircleRadius γ (airyTimeScale t) N),
      ‖airyCosineNumerator L H (t : ℂ) z‖ ≤
        cosineAngularConstant L H (airyTimeScale t) * ‖cosineRegulator γ (airyTimeScale t) z‖ := by
  have hτ := airyTimeScale_pos_of_pos ht
  filter_upwards [(cosineCircleRadius_tendsto hγ hτ).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with N hR hN
  intro z hz
  have hzn : ‖z‖ = cosineCircleRadius γ (airyTimeScale t) N := by
    simpa only [mem_sphere_iff_norm, sub_zero] using! hz
  have h := airyPropagator_matrix_angular L H hH (Complex.sqrt (I * z))
    (circle_root_ne_zero hR hzn) t ht.le
  have hs : Complex.sqrt (I * z) ^ 2 = I * z := Complex.cpow_ofNat_inv_pow _ 2
  rw [hs] at h
  exact h.trans (cosine_angular_exp_le L H hγ hτ hγH N hN hR z hzn)

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
