/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # Actual complex Gaussian mass and translation distance

Demand: LinearOptics10 Lemma 48. The existing fully proved Gaussian
normalization, Hellinger affinity and Cauchy--Schwarz argument is factored
from the OpenQuestions consumer into this shared mathematical layer.
No density normalization, integrability or final distance bound is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift

/-- The actual standard complex Gaussian density with respect to plane volume. -/
noncomputable def density (z : ℂ) : ℝ := Real.pi⁻¹ * Real.exp (-Complex.normSq z)

/-- The complex Gaussian density `density` is nonnegative. -/
theorem nonneg (z : ℂ) : 0 ≤ density z := by
  unfold density
  positivity

/-- The density `density` has integral one. -/
theorem mass : (∫ z : ℂ, density z) = 1 := by
  have hG : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  let g := fun p : ℝ × ℝ => Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have hf (z : ℂ) : density z = g (Complex.measurableEquivRealProd z) := by
    simp only [density, g, Complex.measurableEquivRealProd_apply, Complex.normSq_apply,
      neg_add, Real.exp_add, pow_two]
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp' g
  simp_rw [hf]
  rw [he]
  dsimp [g]
  rw [integral_const_mul]
  change Real.pi⁻¹ * (∫ a : ℝ × ℝ, Real.exp (-a.1 ^ 2) * Real.exp (-a.2 ^ 2)
      ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = 1
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun y : ℝ => Real.exp (-y ^ 2))]
  simp only [hG, ← pow_two, Real.sq_sqrt Real.pi_pos.le]
  exact inv_mul_cancel₀ Real.pi_pos.ne'
/-- The actual independent product density in a finite complex coordinate space. -/
noncomputable def prodDensity (N : ℕ) (x : Fin N → ℂ) : ℝ := ∏ i, density (x i)

/-- The product Gaussian density `prodDensity` has integral one in every dimension. -/
theorem prodMass (N : ℕ) : (∫ x : Fin N → ℂ, prodDensity N x) = 1 := by
  unfold prodDensity
  rw [integral_fintype_prod_volume_eq_prod]
  simp [mass]

/-- The product Gaussian density `prodDensity` is pointwise nonnegative. -/
private theorem prodNonneg (N : ℕ) (x : Fin N → ℂ) :
    0 ≤ prodDensity N x := Finset.prod_nonneg fun i _ => nonneg (x i)

/-- Translating `prodDensity` preserves its integral of one. -/
private theorem shiftMass (N : ℕ) (v : Fin N → ℂ) :
    (∫ x : Fin N → ℂ, prodDensity N (x - v)) = 1 := by
  rw [integral_sub_right_eq_self (prodDensity N), prodMass]

/-- The product of `density` and its translate equals the squared midpoint density times the
stated exponential factor. -/
private theorem overlap (z v : ℂ) :
    density z * density (z - v) = Real.exp (-Complex.normSq v / 2) * density (z - v / 2) ^ 2 := by
  have he : Complex.normSq z + Complex.normSq (z - v)
      = 2 * Complex.normSq (z - v / 2) + Complex.normSq v / 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im]
    norm_num
    ring
  have hE : Real.exp (-Complex.normSq z) * Real.exp (-Complex.normSq (z - v)) =
      Real.exp (-Complex.normSq v / 2) * (Real.exp (-Complex.normSq (z - v / 2))
        * Real.exp (-Complex.normSq (z - v / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    linarith only [he]
  unfold density
  rw [mul_pow, pow_two]
  calc
    _ = (Real.pi⁻¹ * Real.pi⁻¹) * (Real.exp (-Complex.normSq z) * Real.exp (-Complex.normSq (z - v))) := by ring
    _ = _ := by rw [hE]; ring

/-- Expresses the product of `prodDensity` and its translate as the square of a rescaled
midpoint density. -/
private theorem prodOverlap (N : ℕ) (v x : Fin N → ℂ) :
    prodDensity N x * prodDensity N (x - v) =
      (Real.exp (-(∑ i, Complex.normSq (v i)) / 4) * prodDensity N (x - v / 2)) ^ 2 := by
  unfold prodDensity
  rw [← Finset.prod_mul_distrib]
  simp only [Pi.sub_apply, Pi.div_apply, overlap]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow, mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  push_cast
  ring

/-- The affinity of `prodDensity` and its translate is the exponential of minus one quarter of
the squared displacement norm. -/
private theorem affinity (N : ℕ) (v : Fin N → ℂ) :
    (∫ x : Fin N → ℂ, Real.sqrt (prodDensity N x) * Real.sqrt (prodDensity N (x - v)))
      = Real.exp (-(∑ i, Complex.normSq (v i)) / 4) := by
  have he (x : Fin N → ℂ) : Real.sqrt (prodDensity N x) * Real.sqrt (prodDensity N (x - v))
      = Real.exp (-(∑ i, Complex.normSq (v i)) / 4) * prodDensity N (x - v / 2) := by
    apply (sq_eq_sq₀ (by positivity)
      (mul_nonneg (Real.exp_pos _).le (prodNonneg N _))).1
    rw [mul_pow, Real.sq_sqrt (prodNonneg N x),
      Real.sq_sqrt (prodNonneg N (x - v)), prodOverlap]
  simp_rw [he]
  rw [integral_const_mul, shiftMass, mul_one]

/-- The squared integral of the absolute difference between `prodDensity` and its translate is
bounded by twice the squared displacement norm. -/
private theorem prodDistSq (N : ℕ) (v : Fin N → ℂ) :
    (∫ x : Fin N → ℂ, |prodDensity N (x - v) - prodDensity N x|) ^ 2
      ≤ 2 * ∑ i, Complex.normSq (v i) := by
  let p := prodDensity N
  let q := fun x => p (x - v)
  let a := fun x => Real.sqrt (p x) * Real.sqrt (q x)
  let f := fun x => |Real.sqrt (p x) - Real.sqrt (q x)|
  let g := fun x => Real.sqrt (p x) + Real.sqrt (q x)
  let S := ∑ i, Complex.normSq (v i)
  let A := Real.exp (-S / 4)
  have hp0 (x) : 0 ≤ p x := prodNonneg N x
  have hq0 (x) : 0 ≤ q x := prodNonneg N (x - v)
  have hpI : (∫ x, p x) = 1 := prodMass N
  have hqI : (∫ x, q x) = 1 := shiftMass N v
  have haI : (∫ x, a x) = A := affinity N v
  have hp : Integrable p := Integrable.of_integral_ne_zero (by rw [hpI]; norm_num)
  have hq : Integrable q := Integrable.of_integral_ne_zero (by rw [hqI]; norm_num)
  have ha : Integrable a := Integrable.of_integral_ne_zero (by rw [haI]; exact (Real.exp_pos _).ne')
  have hfE (x) : f x ^ 2 = p x + q x - 2 * a x := by
    dsimp [f, a]
    rw [sq_abs]
    nlinarith only [Real.sq_sqrt (hp0 x), Real.sq_sqrt (hq0 x)]
  have hgE (x) : g x ^ 2 = p x + q x + 2 * a x := by
    dsimp [g, a]
    nlinarith only [Real.sq_sqrt (hp0 x), Real.sq_sqrt (hq0 x)]
  have hfC : Continuous f := by dsimp [f, p, q, prodDensity, density]; fun_prop
  have hgC : Continuous g := by dsimp [g, p, q, prodDensity, density]; fun_prop
  have hfInt : Integrable (fun x => f x ^ 2) := by
    simp_rw [hfE]
    exact (hp.add hq).sub (ha.const_mul 2)
  have hgInt : Integrable (fun x => g x ^ 2) := by
    simp_rw [hgE]
    exact (hp.add hq).add (ha.const_mul 2)
  have hfI : (∫ x, f x ^ 2) = 2 - 2 * A := by
    simp_rw [hfE]
    change (∫ x, (p + q) x - 2 * a x) = _
    rw [integral_sub (hp.add hq) (ha.const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add hp hq, integral_const_mul, hpI, hqI, haI]
    ring
  have hgI : (∫ x, g x ^ 2) = 2 + 2 * A := by
    simp_rw [hgE]
    change (∫ x, (p + q) x + 2 * a x) = _
    rw [integral_add (hp.add hq) (ha.const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add hp hq, integral_const_mul, hpI, hqI, haI]
    ring
  have hfLp : MemLp f 2 := (memLp_two_iff_integrable_sq hfC.aestronglyMeasurable).2 hfInt
  have hgLp : MemLp g 2 := (memLp_two_iff_integrable_sq hgC.aestronglyMeasurable).2 hgInt
  have hfg (x) : f x * g x = |q x - p x| := by
    dsimp [f, g]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul]
    have he : (Real.sqrt (p x) - Real.sqrt (q x)) * (Real.sqrt (p x) + Real.sqrt (q x)) = p x - q x := by
      nlinarith only [Real.sq_sqrt (hp0 x), Real.sq_sqrt (hq0 x)]
    rw [he, abs_sub_comm]
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g)
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (Filter.Eventually.of_forall (fun x => abs_nonneg (Real.sqrt (p x) - Real.sqrt (q x))))
    (Filter.Eventually.of_forall (fun x => add_nonneg (Real.sqrt_nonneg (p x)) (Real.sqrt_nonneg (q x))))
    (show MemLp f (ENNReal.ofReal 2) by norm_num; exact hfLp)
    (show MemLp g (ENNReal.ofReal 2) by norm_num; exact hgLp)
  simp only [Real.rpow_two] at hc
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hfI, hgI] at hc
  simp_rw [hfg] at hc
  have hFm : 0 ≤ 2 - 2 * A := by rw [← hfI]; exact integral_nonneg fun x => sq_nonneg _
  have hGm : 0 ≤ 2 + 2 * A := by rw [← hgI]; exact integral_nonneg fun x => sq_nonneg _
  have hI0 : 0 ≤ ∫ x, |q x - p x| := integral_nonneg fun x => abs_nonneg _
  have hCS : (∫ x, |q x - p x|) ^ 2 ≤ 4 * (1 - A ^ 2) := by
    have hroot : 0 ≤ Real.sqrt (2 - 2 * A) * Real.sqrt (2 + 2 * A) := by positivity
    have he : (Real.sqrt (2 - 2 * A) * Real.sqrt (2 + 2 * A)) ^ 2 = 4 * (1 - A ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hFm, Real.sq_sqrt hGm]
      ring
    nlinarith only [hc, hI0, hroot, he]
  have hA : A ^ 2 = Real.exp (-S / 2) := by
    dsimp [A]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have he := Real.add_one_le_exp (-S / 2)
  rw [← hA] at he
  change (∫ x, |q x - p x|) ^ 2 ≤ 2 * S
  nlinarith only [hCS, he]

/-- The total variation distance between the standard product complex Gaussian density and its
translate is at most the Euclidean norm of the displacement. -/
theorem shiftBound : ∀ (N : ℕ) (v : Fin N → ℂ),
    (1 / 2) * ∫ x : Fin N → ℂ,
        |∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i - v i))))
          - ∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i))))|
      ∂MeasureTheory.volume
    ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
  intro N v
  have h1 : ∀ x : Fin N → ℂ,
      (∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i - v i)))))
        = prodDensity N (x - v) := by
    intro x
    simp only [prodDensity, density, Pi.sub_apply]
  have h2 : ∀ x : Fin N → ℂ,
      (∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i)))))
        = prodDensity N x := by
    intro x
    simp only [prodDensity, density]
  have hd := prodDistSq N v
  have hI0 : 0 ≤ ∫ x : Fin N → ℂ, |prodDensity N (x - v) - prodDensity N x| :=
    integral_nonneg fun x => abs_nonneg _
  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  simp only [h1, h2]

  have hu : ((1 / 2) * ∫ x : Fin N → ℂ, |prodDensity N (x - v) - prodDensity N x|) ^ 2
      = (1 / 4) * (∫ x : Fin N → ℂ, |prodDensity N (x - v) - prodDensity N x|) ^ 2 := by
    ring
  have hkey : ((1 / 2) * ∫ x : Fin N → ℂ, |prodDensity N (x - v) - prodDensity N x|) ^ 2
      ≤ ∑ i, Complex.normSq (v i) := by
    linarith [hu, hd, hS0]
  have hnn : 0 ≤ (1 / 2) * ∫ x : Fin N → ℂ,
      |prodDensity N (x - v) - prodDensity N x| := by
    exact mul_nonneg (by norm_num) hI0
  have hsq : Real.sqrt (((1 / 2) * ∫ x : Fin N → ℂ,
        |prodDensity N (x - v) - prodDensity N x|) ^ 2)
      ≤ Real.sqrt (∑ i, Complex.normSq (v i)) :=
    Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq hnn] at hsq


end Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift
