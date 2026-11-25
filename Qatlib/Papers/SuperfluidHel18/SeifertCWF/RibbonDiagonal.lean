/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.NormalRibbon
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonTwist

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The diagonal profile of the ribbon Gauss kernel

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The local model has an even twist term and an odd curvature term. On a
symmetric parameter band the odd term integrates to zero, while the even
term has limiting mass two. With the Gauss normalization this yields the
`1 / (2π)` of the ribbon twist.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge (cross3_apply_zero cross3_apply_one
  cross3_apply_two)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Filter Set MeasureTheory
open scoped Real Topology

/-- The twist coefficient of the diagonal profile of the core–edge integral. -/
def ribbonTwistDensity (γ N : ℝ → Fin 3 → ℝ) (s : ℝ) : ℝ :=
  dot3 (cross3 (deriv γ s) (N s)) (deriv N s)

/-- The curvature coefficient of the part odd in the parameter difference. -/
def ribbonBendDensity (γ N : ℝ → Fin 3 → ℝ) (s : ℝ) : ℝ :=
  dot3 (cross3 (deriv γ s) (deriv (deriv γ) s)) (N s)

/-- The local ribbon profile at signed parameter difference `h` and width `a`
for a unit-speed curve and unit perpendicular framing. -/
def frozenRibbonKernel (γ N : ℝ → Fin 3 → ℝ) (a s h : ℝ) : ℝ :=
  (a ^ 2 * ribbonTwistDensity γ N s + a * h * ribbonBendDensity γ N s) /
    (4 * π * Real.sqrt (h ^ 2 + a ^ 2) ^ 3)

/-- The Gauss normalization of the even diagonal coefficient agrees with
the original twist integral. -/
theorem ribbonTwist_eq_integral_density (γ N : ℝ → Fin 3 → ℝ) :
    ribbonTwist γ N = (1 / (2 * π)) * ∫ s in 0..(2 * π), ribbonTwistDensity γ N s := rfl

/-- Squared Euclidean length agrees with the Cartesian self dot product. -/
private theorem euclideanLength_sq_eq_dot3 (v : Fin 3 → ℝ) :
    euclideanLength v ^ 2 = dot3 v v := by
  rw [euclideanLength, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [dot3, pow_two]

/-- The tangent chord of a unit frame has the exact denominator of the local profile. -/
theorem euclideanLength_tangent_normal {T N : Fin 3 → ℝ}
    (hT : dot3 T T = 1) (hN : dot3 N N = 1) (horth : dot3 T N = 0) (h a : ℝ) :
    euclideanLength (h • T - a • N) = Real.sqrt (h ^ 2 + a ^ 2) := by
  have hsq : euclideanLength (h • T - a • N) ^ 2 = h ^ 2 + a ^ 2 := by
    rw [euclideanLength_sq_eq_dot3, dot3_sub_left, dot3_sub, dot3_sub,
      dot3_smul_left, dot3_smul_left, dot3_smul_left, dot3_smul_left,
      dot3_smul_right, dot3_smul_right, dot3_smul_right, dot3_smul_right,
      dot3_comm N T, hT, hN, horth]
    ring
  rw [← hsq, Real.sqrt_sq (show 0 ≤ euclideanLength (h • T - a • N) from norm_nonneg _)]

/-- The two diagonal profiles have explicit antiderivatives at nonzero width. -/
private theorem hasDerivAt_frozenRibbonPrimitive {a : ℝ} (ha : a ≠ 0)
    (B T x : ℝ) :
    HasDerivAt (fun u : ℝ => (T * u - B * a) / Real.sqrt (u ^ 2 + a ^ 2))
      ((a ^ 2 * T + a * x * B) / Real.sqrt (x ^ 2 + a ^ 2) ^ 3) x := by
  have hd : HasDerivAt (fun u : ℝ => u ^ 2 + a ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).add_const (a ^ 2)
  have hpos : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero ha)
  have hs := (Real.sqrt_pos.2 hpos).ne'
  have hn : HasDerivAt (fun u : ℝ => T * u - B * a) T x := by
    simpa using ((hasDerivAt_id x).const_mul T).sub_const (B * a)
  have hr := hn.div (hd.sqrt hpos.ne') hs
  convert hr using 1
  let R := Real.sqrt (x ^ 2 + a ^ 2)
  have hh : R ^ 2 = x ^ 2 + a ^ 2 := Real.sq_sqrt hpos.le
  change (a ^ 2 * T + a * x * B) / R ^ 3 =
    (T * R - (T * x - B * a) * (2 * x / (2 * R))) / R ^ 2
  have hR : R ≠ 0 := hs
  field_simp
  linear_combination -T * hh

/-- Integration over a symmetric band kills the curvature term exactly
and leaves the twist coefficient multiplied by the mass of the band. -/
theorem integral_frozenRibbonKernel (γ N : ℝ → Fin 3 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (s δ : ℝ) :
    (∫ h in -δ..δ, frozenRibbonKernel γ N a s h) =
      ribbonTwistDensity γ N s / (2 * π) * (δ / Real.sqrt (δ ^ 2 + a ^ 2)) := by
  let B := ribbonBendDensity γ N s
  let T := ribbonTwistDensity γ N s
  let f (h : ℝ) := (a ^ 2 * T + a * h * B) / Real.sqrt (h ^ 2 + a ^ 2) ^ 3
  have hpos (h : ℝ) : 0 < h ^ 2 + a ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg h) (sq_pos_of_ne_zero ha)
  have hc : Continuous f := by
    unfold f
    exact (by fun_prop : Continuous fun h : ℝ => a ^ 2 * T + a * h * B).div
      (by fun_prop) (fun h => pow_ne_zero _ (Real.sqrt_pos.2 (hpos h)).ne')
  have hmul : frozenRibbonKernel γ N a s = fun h => (4 * π)⁻¹ * f h := by
    funext h
    simp only [frozenRibbonKernel, f, B, T, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hmul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_frozenRibbonPrimitive ha B T x) (hc.intervalIntegrable _ _)]
  simp only [neg_sq]
  ring

/-- The symmetric-band mass tends to one as the positive offset tends to zero. -/
theorem tendsto_ribbonBand_mass {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun a : ℝ => δ / Real.sqrt (δ ^ 2 + a ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  have h : ContinuousAt (fun a : ℝ => δ / Real.sqrt (δ ^ 2 + a ^ 2)) 0 := by
    apply continuousAt_const.div (by fun_prop)
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq hδ.le] using hδ.ne'
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq hδ.le, div_self hδ.ne']
    using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- Shrinking the offset at fixed positive band width gives the twist
density with the correct normalization. -/
theorem tendsto_integral_frozenRibbonKernel (γ N : ℝ → Fin 3 → ℝ) (s : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun a => ∫ h in -δ..δ, frozenRibbonKernel γ N a s h)
      (𝓝[>] 0) (𝓝 (ribbonTwistDensity γ N s / (2 * π))) := by
  have hlim := (tendsto_const_nhds (x := ribbonTwistDensity γ N s / (2 * π))).mul
    (tendsto_ribbonBand_mass hδ)
  simp only [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (integral_frozenRibbonKernel γ N (mem_Ioi.mp ha).ne' s δ).symm

/-- After also integrating along one period, the frozen diagonal contribution
is the actual total twist multiplied by the explicit band mass. -/
theorem integral_integral_frozenRibbonKernel (γ N : ℝ → Fin 3 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (δ : ℝ) :
    (∫ s in 0..(2 * π), ∫ h in -δ..δ, frozenRibbonKernel γ N a s h) =
      (δ / Real.sqrt (δ ^ 2 + a ^ 2)) * ribbonTwist γ N := by
  rw [intervalIntegral.integral_congr (fun s _ => integral_frozenRibbonKernel γ N ha s δ),
    ribbonTwist_eq_integral_density, ← mul_assoc]
  have heq (s : ℝ) :
      ribbonTwistDensity γ N s / (2 * π) * (δ / Real.sqrt (δ ^ 2 + a ^ 2)) =
        (δ / Real.sqrt (δ ^ 2 + a ^ 2) * (1 / (2 * π))) * ribbonTwistDensity γ N s := by
    simp only [div_eq_mul_inv, one_mul]
    ring
  rw [intervalIntegral.integral_congr (fun s _ => heq s), intervalIntegral.integral_const_mul]

/-- The positive-width difference quotient along a fixed rescaled parameter
direction converges to the directional derivative. -/
private theorem tendsto_ribbonSlope {f : ℝ → Fin 3 → ℝ} {v : Fin 3 → ℝ} {s : ℝ}
    (hf : HasDerivAt f v s) (x : ℝ) :
    Tendsto (fun a : ℝ => a⁻¹ • (f (s + a * x) - f s)) (𝓝[>] 0) (𝓝 (x • v)) := by
  have hparam : HasDerivAt (fun a : ℝ => s + a * x) x 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const x).const_add s)
  have hd : HasDerivAt (fun a : ℝ => f (s + a * x)) (x • v) 0 :=
    hf.scomp_of_eq 0 hparam (by simp)
  simpa only [zero_add, zero_mul, add_zero] using hd.tendsto_slope_zero_right

set_option maxHeartbeats 500000 in
/-- At a fixed rescaled parameter difference, the actual core–edge Gauss
kernel times the width converges to the twist and curvature profile. The
orientation is the one in the Gauss integral with the centerline first. -/
theorem tendsto_rescaled_normalRibbon_gaussKernel {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : Differentiable ℝ N) (s x : ℝ)
    (hT : dot3 (deriv γ s) (deriv γ s) = 1) (hunit : dot3 (N s) (N s) = 1)
    (horth : dot3 (deriv γ s) (N s) = 0) :
    Tendsto (fun a : ℝ => a * gaussKernel γ (normalRibbonPoint γ N a) (s + a * x) s)
      (𝓝[>] 0) (𝓝 (frozenRibbonKernel γ N 1 s x)) := by
  let T := deriv γ s
  let A := deriv (deriv γ) s
  let U := N s
  let V := deriv N s
  let P (a : ℝ) := deriv γ (s + a * x)
  let Q (a : ℝ) := a⁻¹ • (γ (s + a * x) - γ s)
  let R (a : ℝ) := a⁻¹ • (P a - T)
  let C (a : ℝ) := cross3 (R a) T + cross3 (P a) V
  let D (a : ℝ) := Q a - U
  have hγd := hγ.differentiable (by norm_num)
  have hTcont : ContDiff ℝ 1 (deriv γ) := ContDiff.deriv' hγ
  have hTd := hTcont.differentiable (by norm_num)
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 (x • T)) :=
    tendsto_ribbonSlope (hγd s).hasDerivAt x
  have hR : Tendsto R (𝓝[>] 0) (𝓝 (x • A)) :=
    tendsto_ribbonSlope (hTd s).hasDerivAt x
  have hP : Tendsto P (𝓝[>] 0) (𝓝 T) := by
    have hcp : Continuous P := (hγ.continuous_deriv (by norm_num)).comp (by fun_prop)
    have hcp₀ : ContinuousAt P 0 := hcp.continuousAt
    simpa only [P, T, zero_mul, add_zero] using
      hcp₀.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hD : Tendsto D (𝓝[>] 0) (𝓝 (x • T - U)) := hQ.sub tendsto_const_nhds
  have hnum : Tendsto (fun a => dot3 (C a) (D a)) (𝓝[>] 0)
      (𝓝 (dot3 (cross3 (x • A) T + cross3 T V) (x • T - U))) := by
    let g (y : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
      dot3 (cross3 y.1 T + cross3 y.2.1 V) y.2.2
    have hc : Continuous g := by
      simp only [g, dot3, Pi.add_apply, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
      fun_prop
    have hx := hR.prodMk_nhds (hP.prodMk_nhds hD)
    have hy := (hc.continuousAt (x := (x • A, T, x • T - U))).tendsto.comp hx
    simpa only [Function.comp_def, g, C] using hy
  have hlenAt : ContinuousAt euclideanLength (x • T - U) :=
    continuous_euclideanLength.continuousAt
  have hden : Tendsto (fun a => 4 * π * euclideanLength (D a) ^ 3) (𝓝[>] 0)
      (𝓝 (4 * π * euclideanLength (x • T - U) ^ 3)) :=
    tendsto_const_nhds.mul ((hlenAt.tendsto.comp hD).pow 3)
  have hlen := euclideanLength_tangent_normal hT hunit horth x 1
  rw [one_smul, one_pow] at hlen
  rw [hlen] at hden
  have hden0 : 4 * π * Real.sqrt (x ^ 2 + 1) ^ 3 ≠ 0 := by positivity
  have hcoef : dot3 (cross3 (x • A) T + cross3 T V) (x • T - U) =
      ribbonTwistDensity γ N s + x * ribbonBendDensity γ N s := by
    change _ = dot3 (cross3 T U) V + x * dot3 (cross3 T A) U
    simp only [dot3, Pi.add_apply, cross3_apply_zero, cross3_apply_one, cross3_apply_two, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcoef] at hnum
  have hlim := hnum.div hden hden0
  have hval : frozenRibbonKernel γ N 1 s x =
      (ribbonTwistDensity γ N s + x * ribbonBendDensity γ N s) /
        (4 * π * Real.sqrt (x ^ 2 + 1) ^ 3) := by
    simp only [frozenRibbonKernel, one_pow, one_mul]
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := mem_Ioi.mp ha
  have hP_eq : P a = T + a • R a := by
    dsimp only [R]
    rw [smul_smul, mul_inv_cancel₀ ha'.ne', one_smul, add_sub_cancel]
  have hC_eq : cross3 (P a) (T + a • V) = a • C a := by
    rw [show C a = cross3 (R a) T + cross3 (P a) V from rfl, hP_eq]
    funext j
    fin_cases j <;> simp [cross3, Pi.add_apply, Pi.smul_apply] <;> ring
  have hD_eq : γ (s + a * x) - normalRibbonPoint γ N a s = a • D a := by
    change γ (s + a * x) - (γ s + a • U) = a • (a⁻¹ • (γ (s + a * x) - γ s) - U)
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha'.ne', one_smul, sub_sub]
  change dot3 (C a) (D a) / (4 * π * euclideanLength (D a) ^ 3) = _
  rw [gaussKernel, (hasDerivAt_normalRibbonPoint (a := a) (hγd s) (hN s)).deriv,
    show deriv γ (s + a * x) = P a from rfl,
    show deriv γ s + a • deriv N s = T + a • V from rfl,
    hC_eq, hD_eq, dot3_smul_left, dot3_smul_right, euclideanLength_smul, abs_of_pos ha']
  by_cases hzero : euclideanLength (D a) = 0
  · simp [hzero]
  · field_simp [ha'.ne', Real.pi_ne_zero]

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
