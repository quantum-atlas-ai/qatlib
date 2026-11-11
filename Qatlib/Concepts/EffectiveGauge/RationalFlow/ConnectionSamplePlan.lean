/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ForwardConnectionSample

set_option backward.isDefEq.respectTransparency false

/-!
# Connection Sample Plan

Rational Flow constructions for Effective Gauge.
Defines `connectionSampleSpacing`, `connectionSampleAccuracy`, `rationalConnectionForwardSample`.
Proves `connectionSampleSpacing_pos`, `connectionSampleAccuracy_pos`, `connectionSamplePlan_budget`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of connection Sample Spacing in the Rational Flow construction. -/
def connectionSampleSpacing (R2 tolerance : ℚ) : ℚ :=
  min (1/4) (tolerance/(4*(R2+1)))

/-- Definition of connection Sample Accuracy in the Rational Flow construction. -/
def connectionSampleAccuracy (R1 R2 tolerance : ℚ) : ℚ :=
  min (1/2) (min (tolerance/(8*(R1+1))) (tolerance*connectionSampleSpacing R2 tolerance/32))

/-- Definition of rational Connection Forward Sample in the Rational Flow construction. -/
def rationalConnectionForwardSample (center neighbor : Quaternion ℚ) (h : ℚ) : ℚ :=
  ((-center.imI)*(neighbor.re-center.re)+center.re*(neighbor.imI-center.imI)
    -center.imK*(neighbor.imJ-center.imJ)+center.imJ*(neighbor.imK-center.imK))/h

/-- Original `connectionSampleSpacing_pos` guarantee for the `ConnectionSamplePlan` construction; the complete source hypotheses are retained. -/
theorem connectionSampleSpacing_pos (R2 tolerance : ℚ) (hR : 0 ≤ R2) (ht : 0<tolerance) :
    0<connectionSampleSpacing R2 tolerance := by
  apply lt_min (by norm_num)
  exact div_pos ht (by positivity)

/-- Original `connectionSampleAccuracy_pos` guarantee for the `ConnectionSamplePlan` construction; the complete source hypotheses are retained. -/
theorem connectionSampleAccuracy_pos (R1 R2 tolerance : ℚ)
    (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) (ht : 0<tolerance) :
    0<connectionSampleAccuracy R1 R2 tolerance := by
  have hh := connectionSampleSpacing_pos R2 tolerance h2 ht
  apply lt_min (by norm_num)
  exact lt_min (div_pos ht (by positivity)) (by positivity)

/-- These are the executed spacing and accuracy, including all three minima. -/
theorem connectionSamplePlan_budget (R1 R2 tolerance : ℚ)
    (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) (ht : 0<tolerance) :
    let h := connectionSampleSpacing R2 tolerance
    let eta := connectionSampleAccuracy R1 R2 tolerance
    eta ≤ 1/2 ∧ eta*R1+(1+eta)*(h*R2/2+2*eta/h) ≤ tolerance/2 := by
  let h := connectionSampleSpacing R2 tolerance
  let eta := connectionSampleAccuracy R1 R2 tolerance
  have hh : 0<h := connectionSampleSpacing_pos R2 tolerance h2 ht
  have he : 0<eta := connectionSampleAccuracy_pos R1 R2 tolerance h1 h2 ht
  have hehalf : eta ≤ 1/2 := min_le_left _ _
  have he1 : eta ≤ tolerance/(8*(R1+1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have heh : eta ≤ tolerance*h/32 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hh2 : h ≤ tolerance/(4*(R2+1)) := min_le_right _ _
  have hb1 : eta*R1 ≤ tolerance/8 := by
    have ht' := (le_div_iff₀ (by positivity : (0 : ℚ)<8*(R1+1))).mp he1
    nlinarith
  have hb2 : h*R2/2 ≤ tolerance/8 := by
    have ht' := (le_div_iff₀ (by positivity : (0 : ℚ)<4*(R2+1))).mp hh2
    nlinarith
  have hb3 : 2*eta/h ≤ tolerance/16 := by
    apply (div_le_iff₀ hh).mpr
    linarith
  have hbs : h*R2/2+2*eta/h ≤ 3*tolerance/16 := by linarith
  have hm := mul_le_mul_of_nonneg_left hbs (by positivity : (0 : ℚ) ≤ 1+eta)
  have hm2 := mul_le_mul_of_nonneg_right hehalf (by positivity : (0 : ℚ) ≤ 3*tolerance/16)
  exact ⟨hehalf,by nlinarith⟩

noncomputable section
open scoped Quaternion

/-- Original `rationalConnectionForwardSample_cast` guarantee for the `ConnectionSamplePlan` construction; the complete source hypotheses are retained. -/
theorem rationalConnectionForwardSample_cast (center neighbor : Quaternion ℚ) (h : ℚ) :
    (rationalConnectionForwardSample center neighbor h : ℝ)=
      connectionForwardSample (rationalQuaternionCast center) (rationalQuaternionCast neighbor) (h : ℝ) := by
  simp [rationalConnectionForwardSample,connectionForwardSample,Quaternion.inner_def,iAxis,
    rationalQuaternionCast,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,
    Quaternion.imK_mul,div_eq_mul_inv]
  ring

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
