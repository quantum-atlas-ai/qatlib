/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Bounds the bias gadget error both by the prescribed power of the variance-to-degree ratio
and by half the variance. -/
theorem cube_bias_gadget_error {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (hv1 : v ≤ 1/4)
    {d D : ℕ} (hd : 0 < d) (hD : 0 < D) :
    16*(d : ℝ)^2*(2 : ℝ)^(-(a*biasGadgetSize a D v d)) ≤ (v/(d : ℝ))^D ∧
    16*(d : ℝ)^2*(2 : ℝ)^(-(a*biasGadgetSize a D v d)) ≤ v/2 := by
  let x := v/(d : ℝ)
  let z := (d : ℝ)/v
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hx : 0 < x := by dsimp [x]; positivity
  have hxv : x ≤ v := (div_le_self hv.le hdr)
  have hx1 : x ≤ 1 := by linarith only [hxv,hv1]
  have hz : 0 < z := by dsimp [z]; positivity
  have hm := Nat.le_ceil ((4*(D : ℝ)/a)*Real.logb 2 z)
  have hma : 4*(D : ℝ)*Real.logb 2 z ≤ a*biasGadgetSize a D v d := by
    have he := mul_le_mul_of_nonneg_left hm ha.le
    dsimp [biasGadgetSize,z] at he ⊢
    have hc : a*((4*(D : ℝ)/a)*Real.logb 2 ((d : ℝ)/v))=4*(D : ℝ)*Real.logb 2 ((d : ℝ)/v) := by
      field_simp
    rw [hc] at he
    exact he
  have he : (2 : ℝ)^(-(a*biasGadgetSize a D v d)) ≤ x^(4*D) := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hma)).trans_eq
    rw [show -(4*(D : ℝ)*Real.logb 2 z)=(-Real.logb 2 z)*((4*D : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_natCast,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hz]
    have hzInv : z⁻¹=x := by dsimp [z,x]; simp
    rw [hzInv]
  have h2 : x^(2*D) ≤ x^2 := pow_le_pow_of_le_one hx.le hx1 (by omega)
  have hDD : 16*(d : ℝ)^2*x^(2*D) ≤ 1 := by
    have he := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 16*(d : ℝ)^2 by positivity)
    have hxd : (d : ℝ)^2*x^2=v^2 := by dsimp [x]; field_simp
    nlinarith only [he,hxd,hv.le,hv1]
  have hmain : 16*(d : ℝ)^2*(2 : ℝ)^(-(a*biasGadgetSize a D v d)) ≤ x^(2*D) := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 16*(d : ℝ)^2 by positivity)
    have hg := mul_le_mul_of_nonneg_right hDD (pow_nonneg hx.le (2*D))
    have hp : x^(4*D)=x^(2*D)*x^(2*D) := by rw [← pow_add]; congr 1; omega
    rw [hp] at hh
    nlinarith only [hh,hg]
  refine ⟨hmain.trans (pow_le_pow_of_le_one hx.le hx1 (by omega)),hmain.trans ?_⟩
  have hvSq : x^2 ≤ v^2 := pow_le_pow_left₀ hx.le hxv 2
  nlinarith only [h2,hvSq,hv.le,hv1]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
