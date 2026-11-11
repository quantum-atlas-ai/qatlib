/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.TerminalCircleSamples

/-! # Original source bounds control the terminal circle derivative -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `variation_endpoint_le` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
private theorem variation_endpoint_le (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K H : CoefficientPath) :
    ‖pathVariation (pathTransport q₀ h₀ K) H transportFinish‖ ≤ physicalPeriod*‖H‖ := by
  rw [pathVariation_apply,norm_mul,pathTransport_unit q₀ h₀ K transportFinish,mul_one]
  calc
    _ ≤ ‖H‖*|physicalPeriod-0| := norm_integral_le_of_norm_le_const (fun u _ => by
      simp only [norm_mul,Quaternion.norm_star,spinOfVector_norm,extendPath,pathTransport_unit,one_mul,mul_one]
      exact H.norm_coe_le_norm _)
    _ = _ := by rw [sub_zero,abs_of_pos physicalPeriod_pos]; ring

/-- Original `position_y_hasDerivAt` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
private theorem position_y_hasDerivAt (z t y : ℝ) :
    HasDerivAt (fun s => sourcePosition (transversePair (s,z),t)) (EuclideanSpace.single 1 1) y := by
  apply (sourcePosition.hasFDerivAt.comp_hasDerivAt y
    ((transversePair_hasDerivAt z y).prodMk (hasDerivAt_const y t))).congr_deriv
  ext i; fin_cases i <;> rfl

/-- Original `horizontal_y_hasDerivAt` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
private theorem horizontal_y_hasDerivAt (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (y z t : ℝ) :
    let p := sourcePosition (transversePair (y,z),t)
    HasDerivAt (fun s => sourceHorizontalQuaternion v (sourcePosition (transversePair (s,z),t)))
      ((-1/2 : ℝ) •
        (spinOfVector (fderiv ℝ v p (EuclideanSpace.single 1 1))*sourceXDerivative v p+
          sourceQuaternion v p*spinOfVector (fderiv ℝ (sourcePhysicalDx v) p (EuclideanSpace.single 1 1)))) y := by
  have hp := position_y_hasDerivAt z t y
  have hq := spinOfVector_hasDerivAt ((hv.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hp)
  have hdx : ContDiff ℝ ∞ (sourcePhysicalDx v) :=
    (hv.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const
  have hd := spinOfVector_hasDerivAt ((hdx.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hp)
  have heq : (fun s => sourceXDerivative v (sourcePosition (transversePair (s,z),t)))=
      (fun s => spinOfVector (sourcePhysicalDx v (sourcePosition (transversePair (s,z),t)))) := by
    funext s
    exact sourceXDerivative_eq_spin v hv _
  have hd' : HasDerivAt (fun s => sourceXDerivative v (sourcePosition (transversePair (s,z),t)))
      (spinOfVector (fderiv ℝ (sourcePhysicalDx v) (sourcePosition (transversePair (y,z),t)) (EuclideanSpace.single 1 1))) y := by
    rw [heq]
    exact hd
  convert (hq.mul hd').const_smul (-1/2 : ℝ) using 1 <;> rfl

/-- Original `horizontal_y_norm` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
private theorem horizontal_y_norm (s sy sx sxy : ℍ) (hs : ‖s‖=1) (m1 m2 : ℝ)
    (hm1 : 0 ≤ m1) (hy : ‖sy‖ ≤ m1) (hx : ‖sx‖ ≤ m1) (hxy : ‖sxy‖ ≤ m2) :
    ‖(-1/2 : ℝ) • (sy*sx+s*sxy)‖ ≤ (m1^2+m2)/2 := by
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_nonpos (by norm_num : (-1/2 : ℝ) ≤ 0),neg_div,neg_neg]
  have h := norm_add_le (sy*sx) (s*sxy)
  rw [norm_mul,norm_mul,hs,one_mul] at h
  have hp : ‖sy‖*‖sx‖ ≤ m1*m1 := mul_le_mul hy hx (norm_nonneg _) hm1
  nlinarith

/-- Original `position_cube` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
private theorem position_cube (y z : ℝ) (hy : y ∈ Icc 0 physicalPeriod) (hz : z ∈ Icc 0 physicalPeriod)
    (t : TransportTime) : InFundamentalCube (sourcePosition (transversePair (y,z),t)) := by
  intro i
  fin_cases i
  · exact t.2
  · exact hy
  · exact hz

/-- A source-only estimate on the coefficient-path directional derivative.
The isometric spin representation identifies its actual pointwise derivative. -/
private theorem coefficient_y_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceRescalingBounds v m1 m2) (y z : ℝ) (hy : y ∈ Icc 0 physicalPeriod) (hz : z ∈ Icc 0 physicalPeriod) :
    ‖fderiv ℝ (horizontalCoefficientPaths v hv) (transversePair (y,z)) (EuclideanSpace.single 0 1)‖ ≤ (m1^2+m2)/2 := by
  let H := fderiv ℝ (horizontalCoefficientPaths v hv) (transversePair (y,z)) (EuclideanSpace.single 0 1)
  have hpath : HasDerivAt (fun s => horizontalCoefficientPaths v hv (transversePair (s,z))) H y :=
    ((contDiff_horizontalCoefficientPaths v hv).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y
      (transversePair_hasDerivAt z y)
  apply (ContinuousMap.norm_le (C := (m1^2+m2)/2) H (by positivity)).mpr
  intro t
  let p := sourcePosition (transversePair (y,z),t)
  have hpc : InFundamentalCube p := position_cube y z hy hz t
  have heval := spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y
    ((ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp_hasDerivAt y hpath)
  change HasDerivAt (fun s => spinOfVector (horizontalCoefficientPaths v hv (transversePair (s,z)) t))
    (spinOfVector (H t)) y at heval
  have hfun : (fun s => spinOfVector (horizontalCoefficientPaths v hv (transversePair (s,z)) t))=
      (fun s => sourceHorizontalQuaternion v (sourcePosition (transversePair (s,z),t))) :=
    funext (fun s => horizontalCoefficientPaths_embed v hv hu _ t)
  rw [hfun] at heval
  have he := heval.unique (horizontal_y_hasDerivAt v hv y z t)
  have hunit : ‖sourceQuaternion v p‖=1 := (spinOfVector_norm _).trans (hu p)
  have hsy : ‖spinOfVector (fderiv ℝ v p (EuclideanSpace.single 1 1))‖ ≤ m1 := by
    rw [spinOfVector_norm]
    exact hb.1 p hpc 1
  have hsx : ‖sourceXDerivative v p‖ ≤ m1 := by
    rw [sourceXDerivative_eq_spin v hv,spinOfVector_norm]
    exact hb.1 p hpc 0
  have hsxy : ‖spinOfVector (fderiv ℝ (sourcePhysicalDx v) p (EuclideanSpace.single 1 1))‖ ≤ m2 := by
    rw [spinOfVector_norm]
    exact hb.2 p hpc 1
  calc
    ‖H t‖ = ‖spinOfVector (H t)‖ := (spinOfVector_norm _).symm
    _ = _ := congrArg norm he
    _ ≤ _ := horizontal_y_norm _ _ _ _ hunit m1 m2 hm1 hsy hsx hsxy

/-- Original `terminalRatio_y_derivative_bound` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
theorem terminalRatio_y_derivative_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceRescalingBounds v m1 m2) (y z : ℝ) (hy : y ∈ Icc 0 physicalPeriod) (hz : z ∈ Icc 0 physicalPeriod) :
    ‖fderiv ℝ (terminalRatio v hv q₀ h₀) (transversePair (y,z)) (EuclideanSpace.single 0 1)‖ ≤
      physicalPeriod*((m1^2+m2)/2) := by
  let F := horizontalCoefficientPaths v hv
  let p := transversePair (y,z)
  let K := F p
  let H := fderiv ℝ F p (EuclideanSpace.single 0 1)
  have hpath : HasDerivAt (fun s => F (transversePair (s,z))) H y :=
    ((contDiff_horizontalCoefficientPaths v hv).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt y
      (transversePair_hasDerivAt z y)
  have htransport := (pathTransport_hasFDerivAt q₀ h₀ K).comp_hasDerivAt y hpath
  have heval := ((ContinuousMap.evalCLM ℝ transportFinish).hasFDerivAt.comp_hasDerivAt y htransport).mul_const (star q₀)
  change HasDerivAt (fun s => terminalRatio v hv q₀ h₀ (transversePair (s,z)))
    (pathVariation (pathTransport q₀ h₀ K) H transportFinish*star q₀) y at heval
  have hactual := ((contDiff_terminalRatio v hv q₀ h₀).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt y
    (transversePair_hasDerivAt z y)
  have he := hactual.unique heval
  rw [he,norm_mul,Quaternion.norm_star,h₀,mul_one]
  exact (variation_endpoint_le q₀ h₀ K H).trans (mul_le_mul_of_nonneg_left
    (coefficient_y_bound v hv hu m1 m2 hm1 hm2 hb y z hy hz) physicalPeriod_pos.le)

/-- Original `rescaledTerminalRatio_y_bound` guarantee for the `TerminalRegularity` construction; the complete source hypotheses are retained. -/
theorem rescaledTerminalRatio_y_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (y z : ℝ) (hy : y ∈ Icc 0 1) (hz : z ∈ Icc 0 1) :
    ‖fderiv ℝ (rescaledTerminalRatio v hv hu source hs m1 m2) (transversePair (y,z))
      (EuclideanSpace.single 0 1)‖ ≤ ((((7*m1)^2+49*m2)/2 : ℚ) : ℝ) := by
  have hm1R : (0 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hm2R : (0 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hY : physicalPeriod*y ∈ Icc 0 physicalPeriod :=
    ⟨mul_nonneg physicalPeriod_pos.le hy.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 physicalPeriod_pos.le⟩
  have hZ : physicalPeriod*z ∈ Icc 0 physicalPeriod :=
    ⟨mul_nonneg physicalPeriod_pos.le hz.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 physicalPeriod_pos.le⟩
  have h := terminalRatio_y_derivative_bound v hv hu (rescaledOriginSeed v source m1 m2)
    (rescaledOriginSeed_spec v hu source hs m1 m2).1 (m1 : ℝ) (m2 : ℝ) hm1R hm2R hb (physicalPeriod*y) (physicalPeriod*z) hY hZ
  change ‖fderiv ℝ (fun p => terminalRatio v hv (rescaledOriginSeed v source m1 m2)
      (rescaledOriginSeed_spec v hu source hs m1 m2).1 (physicalPeriod • p)) _ _‖ ≤ _
  rw [fderiv_scaled_argument _ (contDiff_terminalRatio v hv _ _) physicalPeriod,
    norm_smul,Real.norm_eq_abs,abs_of_pos physicalPeriod_pos,transversePair_scale]
  have hp : physicalPeriod ≤ (7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have hp2 : physicalPeriod^2 ≤ (49 : ℝ) := by
    simpa only [show (7 : ℝ)^2=49 by norm_num] using (sq_le_sq₀ physicalPeriod_pos.le (by norm_num : (0 : ℝ) ≤ 7)).mpr hp
  apply (mul_le_mul_of_nonneg_left h physicalPeriod_pos.le).trans
  push_cast
  have hc := mul_le_mul_of_nonneg_right hp2 (show (0 : ℝ) ≤ ((m1 : ℝ)^2+(m2 : ℝ))/2 by positivity)
  nlinarith only [hc]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
