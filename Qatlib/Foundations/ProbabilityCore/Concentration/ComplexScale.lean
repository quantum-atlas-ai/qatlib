/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section


/-! # Actual complex Gaussian variance scaling

Demand: LinearOptics10 Lemma 48. A smaller-variance Gaussian is dominated
pointwise by the original density divided by its volume scale. Actual Haar
change of variables proves unit mass; integration and Bernoulli's inequality
then bound total variation, including the zero-dimensional product.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Qatlib.Foundations.ProbabilityCore.Concentration.ComplexScale
open Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift

/-- The actual complex Gaussian scaled by a positive real standard deviation. -/
def scaled (s : ℝ) (z : ℂ) : ℝ := (s^2)⁻¹ * density (z/(s : ℂ))

/-- The scaled density is actually nonnegative. -/
theorem scaledNonneg (s : ℝ) (z : ℂ) : 0 ≤ scaled s z := by
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg s)) (nonneg _)

/-- The actual change of variables has the real two-dimensional complex volume factor. -/
theorem scaledMass {s : ℝ} (hs : 0 < s) : (∫ z : ℂ, scaled s z ∂volume) = 1 := by
  have hc : (fun z : ℂ => density (z/(s : ℂ))) = fun z => density (s⁻¹ • z) := by
    funext z
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have hm : (∫ z : ℂ, density (z/(s : ℂ)) ∂volume) = s^2 := by
    rw [hc]
    simpa [Complex.finrank_real_complex, abs_of_pos hs, mass,
      smul_eq_mul] using Measure.integral_comp_inv_smul (volume : Measure ℂ) density s
  unfold scaled
  rw [integral_const_mul, hm, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]

/-- A scaled smaller-variance density is pointwise dominated after multiplying by s squared. -/
theorem domination {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (z : ℂ) :
    s^2 * scaled s z ≤ density z := by
  have hsq : 0 < s^2 := sq_pos_of_pos hs
  have hsq1 : s^2 ≤ 1 := by nlinarith
  have hn : Complex.normSq z ≤ Complex.normSq z / s^2 :=
    (le_div_iff₀ hsq).mpr (mul_le_of_le_one_right (Complex.normSq_nonneg _) hsq1)
  have he : Real.exp (-Complex.normSq (z/(s : ℂ))) ≤ Real.exp (-Complex.normSq z) := by
    apply Real.exp_le_exp.mpr
    simp only [map_div₀, Complex.normSq_ofReal]
    simpa [pow_two] using neg_le_neg hn
  calc
    s^2 * scaled s z = density (z/(s : ℂ)) := by
      rw [scaled, ← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]
    _ ≤ density z := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr Real.pi_pos.le)

/-- The actual independent scaled product has unit integral in every finite dimension. -/
theorem productMass (N : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ x : Fin N → ℂ, ∏ i, scaled s (x i) ∂volume) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [scaledMass hs]

/-- The true density comparison multiplies over the actual independent coordinates. -/
theorem productDom (N : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (x : Fin N → ℂ) :
    s^(2*N) * (∏ i, scaled s (x i)) ≤ prodDensity N x := by
  have h := Finset.prod_le_prod₀
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      mul_nonneg (sq_nonneg s) (scaledNonneg s (x i)))
    (fun i _ => domination hs hs1 (x i))
  simpa [Finset.prod_mul_distrib, pow_mul, prodDensity] using h

/-- The full source variance-scaling target follows from real densities and their actual mass. -/
theorem scalingBound (N : ℕ) {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) :
    (1/2) * ∫ x : Fin N → ℂ,
      |(∏ i, scaled (1-eps) (x i)) - prodDensity N x| ∂volume ≤ 2*(N : ℝ)*eps := by
  let s := 1-eps
  let c := s^(2*N)
  let p := prodDensity N
  let q := fun x : Fin N → ℂ => ∏ i, scaled s (x i)
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hc1 : c ≤ 1 := pow_le_one₀ hs.le hs1
  have hq0 (x) : 0 ≤ q x := Finset.prod_nonneg fun i _ => scaledNonneg s (x i)
  have hpI : (∫ x, p x ∂volume) = 1 := prodMass N
  have hqI : (∫ x, q x ∂volume) = 1 := productMass N hs
  have hp : Integrable p := Integrable.of_integral_ne_zero (by rw [hpI]; norm_num)
  have hq : Integrable q := Integrable.of_integral_ne_zero (by rw [hqI]; norm_num)
  have hpoint (x) : |q x-p x| ≤ p x+(1-2*c)*q x := by
    have hd : c*q x ≤ p x := productDom N hs hs1 x
    have hpos : 0 ≤ (1-c)*q x := mul_nonneg (by linarith) (hq0 x)
    apply abs_le.mpr
    constructor <;> nlinarith
  have hi := integral_mono (hq.sub hp).abs (hp.add (hq.const_mul (1-2*c))) hpoint
  have hr : (∫ x, p x+(1-2*c)*q x ∂volume) = 2*(1-c) := by
    rw [integral_add hp (hq.const_mul _), integral_const_mul, hpI, hqI]
    ring
  change (∫ x, |q x-p x| ∂volume) ≤ (∫ x, p x+(1-2*c)*q x ∂volume) at hi
  rw [hr] at hi
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -eps by linarith) (2*N)
  have hbern : 1 - 2*(N : ℝ)*eps ≤ c := by
    dsimp [c,s]
    convert hb using 1
    push_cast
    ring
  change (1/2) * (∫ x, |q x-p x| ∂volume) ≤ 2*(N : ℝ)*eps
  linarith

end Qatlib.Foundations.ProbabilityCore.Concentration.ComplexScale
