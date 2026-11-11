/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhysicalLine
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Forward Connection Sample

Rational Flow constructions for Effective Gauge.
Defines `connectionForwardSample`.
Proves `forwardQuotient_error`, `quaternionForwardQuotient_error`, `connectionForwardSample_error`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Quaternion
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- The actual forward quotient has the half-spacing error. This is the
constant needed by the executed four-value connection sampler. -/
theorem forwardQuotient_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f df ddf : ℝ → E)
    (hdf : ∀ t, HasDerivAt f (df t) t) (hddf : ∀ t, HasDerivAt df (ddf t) t)
    (h : ℝ) (hh : 0<h) (R : ℝ)
    (hb : ∀ t ∈ Icc (0 : ℝ) h, ‖ddf t‖ ≤ R) :
    ‖h⁻¹ • (f h-f 0)-df 0‖ ≤ h*R/2 := by
  have hc : Continuous df := continuous_iff_continuousAt.mpr (fun t => (hddf t).continuousAt)
  have hLip (t : ℝ) (ht : t∈Icc (0 : ℝ) h) : ‖df t-df 0‖ ≤ R*t := by
    have he := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := h) (f := df) (f' := ddf)
      (fun s _ => (hddf s).hasDerivWithinAt)
      (fun s hs => hb s ⟨hs.1,hs.2.le⟩) t ht
    simpa only [sub_zero] using he
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdf t)
    (hc.intervalIntegrable 0 h)
  have hr : (∫ t in (0 : ℝ)..h, df t-df 0)=f h-f 0-h • df 0 := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),hi,intervalIntegral.integral_const,sub_zero]
  have hbint : ‖f h-f 0-h • df 0‖ ≤ R*h^2/2 := by
    rw [← hr]
    have he := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hh.le
      (Filter.Eventually.of_forall (fun t ht => hLip t ⟨ht.1.le,ht.2⟩))
      ((continuous_const.mul continuous_id).intervalIntegrable 0 h)
    calc
      _ ≤ ∫ t in (0 : ℝ)..h, R*t := he
      _ = R*h^2/2 := by
        rw [intervalIntegral.integral_const_mul,integral_id]
        ring
  have hid : h⁻¹ • (f h-f 0)-df 0=h⁻¹ • (f h-f 0-h • df 0) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ hh.ne',one_smul]
  rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
  calc
    _ ≤ h⁻¹*(R*h^2/2) := mul_le_mul_of_nonneg_left hbint (inv_nonneg.mpr hh.le)
    _ = h*R/2 := by field_simp [hh.ne']

/-- Original `quaternionForwardQuotient_error` guarantee for the `ForwardConnectionSample` construction; the complete source hypotheses are retained. -/
theorem quaternionForwardQuotient_error (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (x : SpatialPoint) (j : Fin 3) (h R : ℝ) (hh : 0<h)
    (hb : ∀ y, ‖spatialWordPartial q [j,j] y‖ ≤ R) :
    ‖h⁻¹ • (q (x+h • EuclideanSpace.single j 1)-q x)-spatialWordPartial q [j] x‖ ≤
      h*R/2 := by
  let e : SpatialPoint := EuclideanSpace.single j 1
  have hd (f : QuaternionField) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
      HasDerivAt (fun s : ℝ => f (x+s • e)) (spatialWordPartial f [j] (x+t • e)) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • e) e t := by
      simpa using (((hasDerivAt_id t).smul_const e).const_add x)
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      hline
  have hdd (t : ℝ) : HasDerivAt (fun s : ℝ => spatialWordPartial q [j] (x+s • e))
      (spatialWordPartial q [j,j] (x+t • e)) t :=
    hd (spatialWordPartial q [j]) (contDiff_spatialWordPartial q hq [j]) t
  simpa only [zero_smul,add_zero] using forwardQuotient_error
    (fun t => q (x+t • e)) (fun t => spatialWordPartial q [j] (x+t • e))
    (fun t => spatialWordPartial q [j,j] (x+t • e)) (hd q hq) hdd h hh R
    (fun t _ => hb _)

/-- Definition of connection Forward Sample in the Rational Flow construction. -/
def connectionForwardSample (center neighbor : ℍ) (h : ℝ) : ℝ :=
  inner ℝ (iAxis*center) (h⁻¹ • (neighbor-center))

/-- Approximate centers are not assumed unit. Only the true field is unit. -/
theorem connectionForwardSample_error (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (x : SpatialPoint) (j : Fin 3) (R1 R2 h eta : ℝ)
    (hh : 0<h) (he : 0 ≤ eta)
    (hR1 : ‖spatialWordPartial q [j] x‖ ≤ R1)
    (hR2 : ∀ y, ‖spatialWordPartial q [j,j] y‖ ≤ R2)
    (center neighbor : ℍ) (hc : ‖center-q x‖ ≤ eta)
    (hn : ‖neighbor-q (x+h • EuclideanSpace.single j 1)‖ ≤ eta) :
    |connectionForwardSample center neighbor h-connection q x j| ≤
      eta*R1+(1+eta)*(h*R2/2+2*eta/h) := by
  let y := x+h • EuclideanSpace.single j 1
  let v := spatialWordPartial q [j] x
  let exactD := h⁻¹ • (q y-q x)
  let approxD := h⁻¹ • (neighbor-center)
  have hfd : ‖exactD-v‖ ≤ h*R2/2 := quaternionForwardQuotient_error q hq x j h R2 hh hR2
  have hd : ‖approxD-v‖ ≤ h*R2/2+2*eta/h := by
    have hid : approxD-v=h⁻¹ • ((neighbor-q y)-(center-q x))+(exactD-v) := by
      dsimp only [approxD,exactD]
      simp only [smul_sub]
      abel
    have ha : ‖h⁻¹ • ((neighbor-q y)-(center-q x))‖ ≤ 2*eta/h := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
      have ht := (norm_sub_le (neighbor-q y) (center-q x)).trans (add_le_add hn hc)
      calc
        _ ≤ h⁻¹*(eta+eta) := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hh.le)
        _ = 2*eta/h := by ring
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  have hcn : ‖center‖ ≤ 1+eta := by
    have ht := (norm_le_norm_sub_add center (q x)).trans (add_le_add hc (hu x).le)
    linarith
  have hid : connectionForwardSample center neighbor h-connection q x j=
      inner ℝ (iAxis*(center-q x)) v+inner ℝ (iAxis*center) (approxD-v) := by
    simp only [connectionForwardSample,connection,spatialPartial,connectionValue,
      mul_sub,inner_sub_left,inner_sub_right,approxD,v,spatialWordPartial]
    ring
  rw [hid]
  have hfirst : |inner ℝ (iAxis*(center-q x)) v| ≤ eta*R1 := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_mul,norm_iAxis,one_mul]
    exact mul_le_mul hc hR1 (norm_nonneg _) he
  have hsecond : |inner ℝ (iAxis*center) (approxD-v)| ≤ (1+eta)*(h*R2/2+2*eta/h) := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_mul,norm_iAxis,one_mul]
    exact mul_le_mul hcn hd (norm_nonneg _) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
