/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselProfile

import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Ring

/-!
# The derivative identity connecting the two Bessel force profiles

[Saenz2021HydroSpinLattices], equations (14) and (17),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
The first-order Bessel memory kernel agrees, with the paper's sign, with
the derivative of the zeroth-order spatial wave profile. The proof uses
the coefficient shift in Mathlib's entire regularized hypergeometric series.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

open Complex FormalMultilinearSeries

/-- Differentiation of the entire zero-numerator hypergeometric series
shifts its single denominator parameter by one at the coefficient level. -/
private theorem hg_coeff_succ (b : ℂ) (n : ℕ) :
    (n + 1 : ℕ) • regularizedHGFunCoeff 0 {b} (n + 1) =
      regularizedHGFunCoeff 0 {b + 1} n := by
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton, nsmul_eq_mul,
    Nat.factorial_succ, Nat.cast_mul]
  rw [show b + ((n + 1 : ℕ) : ℂ) = b + 1 + (n : ℂ) by push_cast; ring]
  rw [mul_assoc, ← mul_div_assoc]
  exact mul_div_mul_left 1 _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

/-- The derivative of the entire regularized `₀F₁` function is the
regularized `₀F₁` with the denominator parameter incremented. -/
private theorem deriv_regularized_hg (b z : ℂ) :
    deriv (regularizedHGFun 0 {b}) z = regularizedHGFun 0 {b + 1} z := by
  let p := regularizedHGFunSeries 0 {b}
  let q := regularizedHGFunSeries 0 {b + 1}
  have hr : p.radius = ⊤ := radius_regularizedHGFunSeries_zero_eq_top
  have hr' : q.radius = ⊤ := radius_regularizedHGFunSeries_zero_eq_top
  have hz : ‖z‖ₑ < p.radius := by rw [hr]; exact enorm_lt_top
  have hp : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using
      hz.trans_le p.radius_le_radius_derivSeries
  have hq : z ∈ Metric.eball (0 : ℂ) q.radius := by
    rw [hr']
    exact Metric.mem_eball.mpr (edist_lt_top _ _)
  let ev := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have hs := (p.derivSeries.hasSum hp).map ev ev.continuous
  have hc (n : ℕ) : p.derivSeries n (fun _ => z) 1 = q n (fun _ => z) := by
    have hsmul := (p.derivSeries n).map_smul_univ (fun _ => z) (fun _ => (1 : ℂ))
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hsmul
    rw [hsmul, _root_.smul_apply]
    change z ^ n • (p.derivSeries.coeff n 1) = _
    rw [derivSeries_coeff_one]
    have hcoeff : p.coeff (n + 1) = regularizedHGFunCoeff 0 {b} (n + 1) :=
      congrFun regularizedHGFunSeries_coeff (n + 1)
    rw [hcoeff, hg_coeff_succ]
    change _ = (ofScalars ℂ (regularizedHGFunCoeff 0 {b + 1}) n) (fun _ => z)
    rw [ofScalars_apply_eq, smul_eq_mul, smul_eq_mul, mul_comm]
  change deriv p.sum z = q.sum z
  rw [← fderiv_apply_one_eq_deriv, p.fderiv_sum hz]
  change ev (p.derivSeries.sum z) = q.sum z
  exact hs.unique ((q.hasSum hq).congr_fun fun n => hc n)

/-- With the standard Bessel normalization, the complex derivative of
`J₀` is `-J₁` everywhere, including at the origin. -/
theorem hasDerivAt_besselJ_zero_neg_besselJ_one (z : ℂ) :
    HasDerivAt (Complex.besselJ 0) (-(Complex.besselJ 1 z)) z := by
  let v := fun x : ℂ => -(x / 2) ^ 2
  have hv : HasDerivAt v (-(z / 2)) z := by
    have h := (((hasDerivAt_id z).div_const (2 : ℂ)).fun_pow 2).neg
    refine h.congr_deriv ?_
    dsimp
    ring
  have hf : HasDerivAt (regularizedHGFun 0 {(1 : ℂ)})
      (regularizedHGFun 0 {(2 : ℂ)} (v z)) (v z) := by
    rw [← show (1 : ℂ) + 1 = 2 by norm_num, ← deriv_regularized_hg]
    exact ((analyticAt_regularizedHGFun_zero (v z))).differentiableAt.hasDerivAt
  have h := hf.comp z hv
  have hfun : Complex.besselJ 0 = fun x => regularizedHGFun 0 {(1 : ℂ)} (v x) := by
    funext x
    simp [Complex.besselJ_def, v]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Complex.besselJ_def, Complex.cpow_one, one_add_one_eq_two, v]
  ring

/-- The real slope used in the Kuramoto force equals the negative of the
first-order Bessel profile used in the past-history force. -/
theorem besselJ0Slope_eq_neg_besselJ1Profile (x : ℝ) :
    besselJ0Slope x = -besselJ1Profile x := by
  rw [besselJ0Slope_eq]
  have h := (hasDerivAt_besselJ_zero_neg_besselJ_one (x : ℂ)).deriv
  simp only [Int.cast_zero] at *
  rw [h]
  exact Complex.neg_re _

/-- The two instantaneous azimuthal force projections can equivalently use
the first-order Bessel profile, with the sign coming from `J₀' = -J₁`. -/
theorem azimuth_forces_eq_besselJ1 (F k r L φi φj : ℝ) :
    leftAzimuthForce F besselJ0Slope k r L φi φj =
      leftAzimuthForce (-F) besselJ1Profile k r L φi φj ∧
    rightAzimuthForce F besselJ0Slope k r L φi φj =
      rightAzimuthForce (-F) besselJ1Profile k r L φi φj := by
  constructor <;>
    simp only [leftAzimuthForce, rightAzimuthForce, besselJ0Slope_eq_neg_besselJ1Profile,
      mul_neg, neg_mul]

end Qatlib.Papers.HydroSpinLatt21.GKModel
