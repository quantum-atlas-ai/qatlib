/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.BinomialKernel

/-!
# Euler integral and the hypergeometric endpoint

This module integrates the polynomial terms `eulerTerm` and sums them to prove `euler_integral`
for the hypergeometric function on [0, 1]. At parameter one, `kernel` becomes the upper
semicircle integrand, giving the exact endpoint value 3π/8.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `euler_integral`: identifies the hypergeometric function with the Euler kernel integral.
* `gauss_endpoint_one`: evaluates the function at one.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom

namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler

/-- Each polynomial Euler-series term is continuous as a function of its integration variable. -/
theorem continuous_eulerTerm (z : ℝ) (n : ℕ) : Continuous (eulerTerm z n) := by
  unfold eulerTerm
  fun_prop

/-- The integral of `eulerTerm z n` from zero to one is the hypergeometric series term `coeff n
* z^n`. -/
theorem eulerTerm_integral (z : ℝ) (n : ℕ) :
    (∫ u in (0:ℝ)..1,eulerTerm z n u)=coeff n*z^n := by
  have he : eulerTerm z n=fun u : ℝ => (3/2:ℝ)*binCoeff n*z^n*(u^(2*n)-u^(2*n+2)) := by
    funext u
    unfold eulerTerm
    rw [pow_add]
    ring
  have h1 : IntervalIntegrable (fun u : ℝ => u^(2*n)) volume 0 1 :=
      (continuous_id.pow _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => u^(2*n+2)) volume 0 1 :=
      (continuous_id.pow _).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub h1 h2,integral_pow,integral_pow]
  simp only [one_pow,zero_pow (by omega : 2*n+1≠0),zero_pow (by omega : 2*n+2+1≠0),
    sub_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [gauss_coeff_from_binomial]
  have hn : (0:ℝ)≤n := by positivity
  field_simp
  ring

/-- For nonnegative `z`, every Euler-series term is nonnegative on [0, 1]. -/
theorem eulerTerm_nonneg {z : ℝ} (hz : 0≤z) (n : ℕ) (u : ℝ) (hu : u∈Set.Icc (0:ℝ) 1) :
    0≤eulerTerm z n u := by
  have hu0 := hu.1
  have hp : 0≤1-u^2 := by nlinarith [hu.1,hu.2]
  have hb := (binCoeff_pos n).le
  unfold eulerTerm
  positivity

/-- For nonnegative `z`, the integral of the norm of `eulerTerm z n` over `(0, 1]` is `coeff n *
z^n`. -/
theorem eulerTerm_norm_integral {z : ℝ} (hz : 0≤z) (n : ℕ) :
    (∫ u,‖eulerTerm z n u‖ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))=coeff n*z^n := by
  have he : (fun u => ‖eulerTerm z n u‖)=ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] eulerTerm z n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.norm_of_nonneg (eulerTerm_nonneg hz n u ⟨hu.1.le,hu.2⟩)
  rw [integral_congr_ae he,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),eulerTerm_integral]

/-- For `z ∈ [0, 1]`, the hypergeometric value `₂F₁(1/2, 1/2; 5/2; z)` is 3/2 times the integral
of `kernel z` from zero to one. This is the Euler representation used for the kernel in
[CrostaSaubanereHuber2026]. -/
theorem euler_integral {z : ℝ} (hz0 : 0≤z) (hz1 : z≤1) :
    ₂F₁ (1/2:ℝ) (1/2) (5/2) z=(3/2:ℝ)*(∫ u in (0:ℝ)..1,kernel z u) := by
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hInt : ∀ n,Integrable (eulerTerm z n) μ := fun n =>
    ((continuous_eulerTerm z n).intervalIntegrable (μ:=volume) 0 1).1
  have hNorm : Summable (fun n : ℕ => ∫ u,‖eulerTerm z n u‖ ∂μ) := by
    simpa only [μ,eulerTerm_norm_integral hz0] using series_summable hz0 hz1
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm hInt hNorm
  have hterms : (fun n : ℕ => ∫ u,eulerTerm z n u ∂μ)=fun n : ℕ => coeff n*z^n := by
    funext n
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),eulerTerm_integral]
  rw [hterms] at hsum
  have he : (∫ u,(∑' n : ℕ,eulerTerm z n u) ∂μ)=(∫ u,(3/2:ℝ)*kernel z u ∂μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (euler_hasSum hz0 hz1 u ⟨hu.1.le,hu.2⟩).tsum_eq
  rw [he] at hsum
  have h := hsum.tsum_eq
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),intervalIntegral.integral_const_mul] at h
  exact (true_series z).trans h

/-- At parameter one, `kernel 1 u` equals `sqrt (1-u^2)` for every real `u`. -/
theorem kernel_one (u : ℝ) : kernel 1 u=Real.sqrt (1-u^2) := by
  simp only [kernel,one_mul,Real.div_sqrt]

/-- For `z ∈ [0, 1]`, the Euler kernel is interval integrable from zero to one. -/
theorem kernel_intervalIntegrable {z : ℝ} (hz0 : 0≤z) (hz1 : z≤1) :
    IntervalIntegrable (kernel z) volume 0 1 := by
  by_cases he : z=1
  · subst z
    change IntervalIntegrable (fun u : ℝ => kernel 1 u) volume 0 1
    simp_rw [kernel_one]
    exact (show Continuous (fun u : ℝ => Real.sqrt (1-u^2)) by fun_prop).intervalIntegrable _ _
  · have hzlt : z<1 := lt_of_le_of_ne hz1 he
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
    unfold kernel
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
    have hzu : z*u^2≤z := mul_le_of_le_one_right hz0 hu2
    exact (Real.sqrt_pos.mpr (by linarith : 0<1-z*u^2)).ne'

/-- The integral of `sqrt (1-u^2)` from zero to one is π/4. -/
theorem half_semicircle_integral :
    (∫ u in (0:ℝ)..1,Real.sqrt (1-u^2))=Real.pi/4 := by
  have hc : Continuous (fun u : ℝ => Real.sqrt (1-u^2)) := by fun_prop
  have h :=
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ:=volume) (-1) 0)
      (hc.intervalIntegrable (μ:=volume) 0 1)
  have he : (∫ u in (-1:ℝ)..0,Real.sqrt (1-u^2))=(∫ u in (0:ℝ)..1,Real.sqrt (1-u^2)) := by
    calc
      _ = ∫ u in (0:ℝ)..1,Real.sqrt (1-(-u)^2) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f:=fun u : ℝ => Real.sqrt (1-u^2)) (a:=0) (b:=1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro u _hu
        exact congrArg Real.sqrt (by ring : (1-(-u)^2:ℝ)=1-u^2)
  rw [he,integral_sqrt_one_sub_sq] at h
  linarith

/-- The endpoint hypergeometric value `₂F₁(1/2, 1/2; 5/2; 1)` is 3π/8. -/
theorem gauss_endpoint_one : ₂F₁ (1/2:ℝ) (1/2) (5/2) 1=3*Real.pi/8 := by
  rw [euler_integral (by norm_num : (0:ℝ)≤1) le_rfl]
  simp_rw [kernel_one]
  rw [half_semicircle_integral]
  ring

end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler
