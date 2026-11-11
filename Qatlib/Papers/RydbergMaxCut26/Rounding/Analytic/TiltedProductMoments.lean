/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.TiltedClosedForm
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product evaluation of tilted Gaussian moments

The scalar functions `massIntegrand` and `crossIntegrand` describe one row of a tilted Gaussian
pair. Independence of the three rows factors the integral of `dotIntegrand` into one cross
moment and two mass moments, producing an explicit formula in terms of `determinant`. See
[CrostaSaubanereHuber2026].

## Main statements

* `dot_product_eval`: factors the three-row tilted dot-product moment.
* `dot_closed`: evaluates this moment for noise scale `√(1 - t²)`.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedMoments
open Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedClosed

/-- The product law of two independent standard real Gaussian variables. -/
abbrev pairLaw : Measure (ℝ×ℝ) := standard1.prod standard1

/-- The linear combination `t * w.1 + s * w.2` of a scalar pair. -/
def yvalue (t s : ℝ) (w : ℝ×ℝ) : ℝ := t*w.1+s*w.2

/-- The exponential weight `exp (-(a * w.1² + b * (yvalue t s w)²))`. -/
def massIntegrand (t s a b : ℝ) (w : ℝ×ℝ) : ℝ := Real.exp (-(a*w.1^2+b*(yvalue t s w)^2))

/-- The scalar cross product `w.1 * yvalue t s w`, multiplied by the tilted mass weight. -/
def crossIntegrand (t s a b : ℝ) (w : ℝ×ℝ) : ℝ := w.1*yvalue t s w*massIntegrand t s a b w

/-- For nonnegative tilt parameters, the mass integrand lies between zero and one. -/
theorem mass_bounds (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (w : ℝ×ℝ) :
    0 ≤ massIntegrand t s a b w ∧ massIntegrand t s a b w ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg ha (sq_nonneg w.1),mul_nonneg hb (sq_nonneg (yvalue t s w))]

/-- For nonnegative tilt parameters, the mass integrand is integrable under the independent
Gaussian pair law. -/
theorem mass_integrable (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (massIntegrand t s a b) pairLaw := by
  apply (integrable_const (1:ℝ)).mono'
  · unfold massIntegrand yvalue
    fun_prop
  · filter_upwards [] with w
    rw [Real.norm_eq_abs,abs_of_nonneg (mass_bounds t s a b ha hb w).1]
    exact (mass_bounds t s a b ha hb w).2

/-- The unweighted scalar cross product is integrable under the independent Gaussian pair law. -/
theorem unweighted_cross_integrable (t s : ℝ) : Integrable (fun w : ℝ×ℝ => w.1*yvalue t s w) pairLaw := by
  have hi : Integrable (fun x : ℝ => x) standard1 :=
      (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have hsq : Integrable (fun x : ℝ => x^2) standard1 :=
      (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  convert! ((hsq.comp_fst standard1).const_mul t).add ((hi.mul_prod hi).const_mul s) using 1
  funext w
  dsimp [yvalue]
  ring

/-- For nonnegative tilt parameters, the cross integrand is integrable under the independent
Gaussian pair law. -/
theorem cross_integrable (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (crossIntegrand t s a b) pairLaw := by
  apply (unweighted_cross_integrable t s).mono
  · unfold crossIntegrand massIntegrand yvalue
    fun_prop
  · filter_upwards [] with w
    simp only [crossIntegrand,norm_mul,Real.norm_eq_abs,abs_of_nonneg (mass_bounds t s a b ha hb w).1]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mass_bounds t s a b ha hb w).2

/-- For nonnegative tilt parameters, the product-measure integral of the mass integrand equals
the iterated moment `pairTiltZero`. -/
theorem mass_product_iterated (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ w,massIntegrand t s a b w ∂pairLaw)=pairTiltZero t s a b := by
  rw [integral_prod _ (mass_integrable t s a b ha hb)]
  rfl

/-- For nonnegative tilt parameters, the product-measure integral of the cross integrand equals
the iterated moment `pairTiltCross`. -/
theorem cross_product_iterated (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ w,crossIntegrand t s a b w ∂pairLaw)=pairTiltCross t s a b := by
  rw [integral_prod _ (cross_integrable t s a b ha hb)]
  rfl

/-- The product law of three independent scalar Gaussian pairs. -/
abbrev pairRowsLaw : Measure (Fin 3 → ℝ×ℝ) := Measure.pi (fun _ : Fin 3 => pairLaw)

/-- The sum of the three scalar cross products, weighted by the exponential of the two tilted
sums of squares. -/
def dotIntegrand (t s a b : ℝ) (R : Fin 3 → ℝ×ℝ) : ℝ :=
  (∑ i, (R i).1*yvalue t s (R i))*
    Real.exp (-(a*(∑ i,(R i).1^2)+b*(∑ i,(yvalue t s (R i))^2)))

/-- The tilted dot-product integrand is the sum of three products, each containing one cross
integrand and two mass integrands. -/
theorem dot_factor (t s a b : ℝ) (R : Fin 3 → ℝ×ℝ) :
    dotIntegrand t s a b R=
      ∑ i : Fin 3,∏ j : Fin 3,if j=i then crossIntegrand t s a b (R j) else massIntegrand t s a b (R j) := by
  have he : Real.exp (-(a*(∑ i,(R i).1^2)+b*(∑ i,(yvalue t s (R i))^2)))=
      ∏ i : Fin 3,massIntegrand t s a b (R i) := by
    simp only [massIntegrand,Fin.prod_univ_three,Fin.sum_univ_three]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold dotIntegrand
  rw [he]
  simp only [Fin.sum_univ_three,Fin.prod_univ_three]
  norm_num [crossIntegrand]
  ring

/-- For nonnegative tilt parameters, each product with one cross integrand and two mass
integrands is integrable under the three-row law. -/
theorem coordinate_integrable (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Fin 3) :
    Integrable (fun R : Fin 3 → ℝ×ℝ =>
      ∏ j : Fin 3,if j=i then crossIntegrand t s a b (R j) else massIntegrand t s a b (R j)) pairRowsLaw := by
  apply Integrable.fintype_prod (f:=fun j (w : ℝ×ℝ) =>
    if j=i then crossIntegrand t s a b w else massIntegrand t s a b w) (μ:=fun _ : Fin 3 => pairLaw)
  intro j
  by_cases hj : j=i
  · simpa only [hj,ite_true] using cross_integrable t s a b ha hb
  · simpa only [hj,ite_false] using mass_integrable t s a b ha hb

/-- For nonnegative tilt parameters, the tilted dot-product integral is three times the cross
moment times the square of the mass moment. -/
theorem dot_product_eval (t s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ R,dotIntegrand t s a b R ∂pairRowsLaw)=
      3*pairTiltCross t s a b*(pairTiltZero t s a b)^2 := by
  simp_rw [dot_factor]
  rw [integral_finsetSum _ (fun i _ => coordinate_integrable t s a b ha hb i)]
  have hi (i j : Fin 3) : (∫ w,(if j=i then crossIntegrand t s a b w else massIntegrand t s a b w) ∂pairLaw)=
      if j=i then pairTiltCross t s a b else pairTiltZero t s a b := by
    by_cases h : j=i
    · simp only [h,ite_true,cross_product_iterated t s a b ha hb]
    · simp only [h,ite_false,mass_product_iterated t s a b ha hb]
  have hterm (i : Fin 3) : (∫ R : Fin 3 → ℝ×ℝ,
      ∏ j : Fin 3,if j=i then crossIntegrand t s a b (R j) else massIntegrand t s a b (R j) ∂pairRowsLaw)=
      ∏ j : Fin 3,if j=i then pairTiltCross t s a b else pairTiltZero t s a b := by
    have h := integral_fintype_prod_eq_prod (μ:=fun _ : Fin 3 => pairLaw)
      (fun j (w : ℝ×ℝ) => if j=i then crossIntegrand t s a b w else massIntegrand t s a b w)
    simpa only [hi] using h
  simp_rw [hterm]
  simp [Fin.sum_univ_three,Fin.prod_univ_three]
  ring

/-- For `|t| < 1` and nonnegative tilt parameters, the three-row tilted dot-product moment with
noise scale `√(1 - t²)` equals `3 * t / (determinant t a b)^(5/2)`, expressed using a square
root. -/
theorem dot_closed (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ R,dotIntegrand t (Real.sqrt (1-t^2)) a b R ∂pairRowsLaw)=
      3*t/((determinant t a b)^2*Real.sqrt (determinant t a b)) := by
  rw [dot_product_eval t _ a b ha hb,pair_mass t a b ht ha hb,pair_cross t a b ht ha hb]
  have hd := determinant_positive t a b ht ha hb
  have hs := Real.sq_sqrt hd.le
  have hz := (Real.sqrt_pos.mpr hd).ne'
  rw [show (1/Real.sqrt (determinant t a b))^2=1/determinant t a b by
    rw [div_pow,one_pow,hs]]
  field_simp
end Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedMoments
