/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticLinkingLimit

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The linking value of the pole and positive real magnetic circles

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The exact rescaling of the angle preserves the Gauss integral. The
integral is constant along the positive real labels and its rescaled
limit is one, giving the oriented value on every physical time slice.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge (cross3_apply_zero cross3_apply_one cross3_apply_two)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussKernel gaussLinking gaussMeasure
  integrable_gaussKernel continuous_gaussKernel)
open MeasureTheory Filter Set
open scoped Topology

/-- The initial positive real circle is smooth in its angle. -/
private theorem contDiff_realLabelMagneticCircle (u : ℝ) :
    ContDiff ℝ 1 (realLabelMagneticCircle u) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun θ => -Real.sin θ / u)
    fun_prop
  · change ContDiff ℝ 1 (fun θ => (Real.sqrt (u ^ 2 + 1) * Real.cos θ - 1) / u)
    fun_prop
  · change ContDiff ℝ 1 (fun θ => -Real.sin θ)
    fun_prop

/-- The pole is smooth in its angle on the initial slice. -/
private theorem contDiff_pole_initial_coords :
    ContDiff ℝ 1 (cartesianCoordinates ∘ magneticPoleCircleAt 0) := by
  have hC : ContDiff ℝ 1 cartesianCoordinates :=
    cartesianCoordinates.toContinuousLinearEquiv.contDiff
  exact hC.comp ((contDiff_magnetic_pole_circle_at_joint.of_le (by simp)).comp
    (contDiff_const.prodMk contDiff_id))

/-- Distinct chart positions make the real-label circle disjoint from
the pole at all angles. -/
private theorem realLabelMagneticCircle_ne_pole (u s t : ℝ) (hu : 0 < u) :
    realLabelMagneticCircle u s ≠ cartesianCoordinates (magneticPoleCircleAt 0 t) := by
  rw [realLabelMagneticCircle_eq u s hu]
  intro h
  exact (Set.disjoint_left.mp (magnetic_circle_disjoint_pole u 0 0 (by positivity)))
    (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self t)

/-- The rescaled Gauss kernel includes exactly the positive Jacobian
factor of the rescaled first angle. -/
private theorem rescaledMagneticGaussKernel_mul (u s t : ℝ) (hu : 0 < u) :
    rescaledMagneticGaussKernel u s t =
      u * gaussKernel (realLabelMagneticCircle u) (cartesianCoordinates ∘ magneticPoleCircleAt 0)
        (u * s) t := by
  let γ := realLabelMagneticCircle u
  have he : rescaledMagneticCircle u = fun x => γ (u * x) :=
    funext fun x => rescaledMagneticCircle_eq u x hu.ne'
  have hγ : DifferentiableAt ℝ γ (u * s) :=
    (contDiff_realLabelMagneticCircle u).differentiable (by norm_num) _
  have hu' : HasDerivAt (fun x : ℝ => u * x) u s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul u
  have hc : HasDerivAt (rescaledMagneticCircle u) (u • deriv γ (u * s)) s := by
    rw [he]
    exact hγ.hasDerivAt.scomp s hu'
  rw [rescaledMagneticGaussKernel_eq u s t hu.ne']
  unfold gaussKernel
  rw [hc.deriv, rescaledMagneticCircle_eq u s hu.ne', ← mul_div_assoc]
  congr 1
  simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two, Pi.smul_apply, smul_eq_mul]
  ring

/-- The rescaled domain is the symmetric angle interval divided by the
positive chart label. -/
private theorem rescaledMagneticInterval_eq (u : ℝ) (hu : 0 < u) :
    rescaledMagneticInterval u = Icc (-Real.pi / u) (Real.pi / u) := by
  ext s
  change |u * s| ≤ Real.pi ↔ -Real.pi / u ≤ s ∧ s ≤ Real.pi / u
  rw [abs_le, div_le_iff₀ hu, le_div_iff₀ hu, mul_comm s u]

/-- The truncated kernel integrates over the same Gauss surface
after shifting the first interval by a period and rescaling its angle. -/
theorem integral_truncatedMagneticGaussKernel_eq (u : ℝ) (hu : 0 < u) :
    (∫ p, truncatedMagneticGaussKernel u p ∂magneticAxisMeasure) =
      gaussLinking (realLabelMagneticCircle u) (cartesianCoordinates ∘ magneticPoleCircleAt 0) := by
  let γ := realLabelMagneticCircle u
  let σ := cartesianCoordinates ∘ magneticPoleCircleAt 0
  let T := 2 * Real.pi
  let a := -Real.pi / u
  let b := Real.pi / u
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let K (s t : ℝ) := gaussKernel γ σ s t
  let L (s t : ℝ) := rescaledMagneticGaussKernel u s t
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) hu.le
  have hγ := contDiff_realLabelMagneticCircle u
  have hne (s t : ℝ) : γ s ≠ σ t := realLabelMagneticCircle_ne_pole u s t hu
  have hK : Integrable (fun p : ℝ × ℝ => K p.1 p.2) (μ.prod μ) :=
    integrable_gaussKernel γ σ hγ contDiff_pole_initial_coords hne
  have hsc : rescaledMagneticCircle u = fun s => γ (u * s) :=
    funext fun s => rescaledMagneticCircle_eq u s hu.ne'
  have hγs : ContDiff ℝ 1 (rescaledMagneticCircle u) := by
    rw [hsc]
    exact hγ.comp (by fun_prop)
  have hL : Continuous (fun p : ℝ × ℝ => L p.1 p.2) := by
    simpa only [L, rescaledMagneticGaussKernel_eq u _ _ hu.ne'] using
      continuous_gaussKernel (rescaledMagneticCircle u) σ hγs contDiff_pole_initial_coords
        (fun s t => by rw [hsc]; exact hne (u * s) t)
  have hLi : Integrable (fun p : ℝ × ℝ => L p.1 p.2)
      ((volume.restrict (Icc a b)).prod μ) := by
    rw [show μ = volume.restrict (Icc (0 : ℝ) T) by rfl, Measure.prod_restrict]
    exact hL.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hperiod : Function.Periodic γ T := by
    intro s
    simp only [γ, T, realLabelMagneticCircle, Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hperiod' : Function.Periodic (deriv γ) T := fun s => by
    rw [← deriv_comp_add_const γ T s]
    rw [show (fun r => γ (r + T)) = γ from funext hperiod]
  have hperK (t : ℝ) : Function.Periodic (fun s => K s t) T := by
    intro s
    simp only [K, gaussKernel, hperiod s, hperiod' s]
  have hInt (t : ℝ) : (∫ s in a..b, L s t) = ∫ s in 0..T, K s t := by
    have ha : u * a = -Real.pi := by dsimp [a]; field_simp
    have hb : u * b = Real.pi := by dsimp [b]; field_simp
    calc
      _ = ∫ s in a..b, u * K (u * s) t := by
        apply intervalIntegral.integral_congr
        intro s _
        exact rescaledMagneticGaussKernel_mul u s t hu
      _ = ∫ s in -Real.pi..Real.pi, K s t := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul, ha, hb] using
          (intervalIntegral.smul_integral_comp_mul_left (f := fun s => K s t) (a := a) (b := b) u)
      _ = _ := by
        have hs : -Real.pi + T = Real.pi := by dsimp [T]; ring
        simpa only [hs, zero_add] using (hperK t).intervalIntegral_add_eq (-Real.pi) 0
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Icc a b
  have hS : MeasurableSet S := measurable_fst measurableSet_Icc
  have hrestrict : (volume.prod μ).restrict S = (volume.restrict (Icc a b)).prod μ := by
    have hdom : S = Icc a b ×ˢ (univ : Set ℝ) := by ext p; simp [S]
    rw [hdom, ← Measure.prod_restrict, Measure.restrict_univ]
  have hId : truncatedMagneticGaussKernel u = S.indicator (fun p => L p.1 p.2) := by
    funext p
    have hInterval : rescaledMagneticInterval u = Icc a b := rescaledMagneticInterval_eq u hu
    by_cases h : p ∈ S
    · have hp : p.1 ∈ rescaledMagneticInterval u := by rw [hInterval]; exact h
      rw [truncatedMagneticGaussKernel, indicator_of_mem hp, indicator_of_mem h]
    · have hp : p.1 ∉ rescaledMagneticInterval u := by rw [hInterval]; exact h
      rw [truncatedMagneticGaussKernel, indicator_of_notMem hp, indicator_of_notMem h]
  change (∫ p, truncatedMagneticGaussKernel u p ∂(volume.prod μ)) =
    (∫ p : ℝ × ℝ, K p.1 p.2 ∂(μ.prod μ))
  rw [hId, integral_indicator hS, hrestrict, integral_prod_symm _ hLi, integral_prod_symm _ hK]
  simp_rw [μ, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hT, hInt]

/-- Every circle on the positive real chart ray has signed Gauss
linking integral one with the oriented initial pole circle. -/
theorem gaussLinking_real_label_pole_eq_one (u : ℝ) (hu : 0 < u) :
    gaussLinking (realLabelMagneticCircle u) (cartesianCoordinates ∘ magneticPoleCircleAt 0) = 1 := by
  have hconst : Tendsto (fun v => ∫ p, truncatedMagneticGaussKernel v p ∂magneticAxisMeasure)
      (𝓝[>] (0 : ℝ))
      (𝓝 (gaussLinking (realLabelMagneticCircle u) (cartesianCoordinates ∘ magneticPoleCircleAt 0))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with v hv
    rw [integral_truncatedMagneticGaussKernel_eq v hv]
    exact gaussLinking_real_label_pole_eq hu hv
  exact tendsto_nhds_unique hconst tendsto_truncatedMagneticGaussIntegral

/-- Conservation transports the actual linking value of the positive
real magnetic circles and the pole to every time slice. -/
theorem gaussLinking_real_magnetic_circle_pole_eq_one (u t : ℝ) (hu : 0 < u) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u 0 t)
      (cartesianCoordinates ∘ magneticPoleCircleAt t) = 1 := by
  rw [gaussLinking_magnetic_circle_pole_eq u 0 t 0 (by positivity)]
  have hr : realLabelMagneticCircle u = cartesianCoordinates ∘ magneticCircleAt u 0 0 :=
    funext fun s => realLabelMagneticCircle_eq u s hu
  rw [← hr]
  exact gaussLinking_real_label_pole_eq_one u hu

end Qatlib.Papers.KnottedLight08.NullLinking
