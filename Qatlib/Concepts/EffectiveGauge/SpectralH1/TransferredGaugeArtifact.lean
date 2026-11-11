/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactDecode
import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactPolynomial

set_option backward.isDefEq.respectTransparency false

/-!
# Transferred Gauge Artifact

Spectral H1 constructions for Effective Gauge.
Defines `TransferredGaugeArtifact`, `rationalQuaternionL1`, `transferredGaugeArtifactValue`.
Proves `rationalQuaternionL1_nonneg`, `rationalQuaternionCast_norm_le_L1`, `transferredGaugeArtifactField_contDiff`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Pure finite payload: no source, lift or PDE evaluator is retained. -/
structure TransferredGaugeArtifact where
  base : RationalGaugeFourierArtifact
  transition : Quaternion ℚ

/-- Definition of rational Quaternion L1 in the Spectral H1 construction. -/
def rationalQuaternionL1 (q : Quaternion ℚ) : ℚ := |q.re|+|q.imI|+|q.imJ|+|q.imK|

/-- Definition of transferred Gauge Artifact Value in the Spectral H1 construction. -/
def transferredGaugeArtifactValue (artifact : TransferredGaugeArtifact) (X : Fin 3 → ℚ)
    (accuracy : ℚ) : Quaternion ℚ :=
  artifact.transition*gaugeFourierArtifactValue artifact.base X
    (accuracy/(rationalQuaternionL1 artifact.transition+1))

noncomputable section
open scoped Quaternion ContDiff

/-- Definition of transferred Gauge Artifact Field in the Spectral H1 construction. -/
def transferredGaugeArtifactField (artifact : TransferredGaugeArtifact) : QuaternionField :=
  fun X => rationalQuaternionCast artifact.transition*gaugeFourierArtifactField artifact.base X

/-- Original `rationalQuaternionL1_nonneg` guarantee for the `TransferredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem rationalQuaternionL1_nonneg (q : Quaternion ℚ) : 0 ≤ rationalQuaternionL1 q := by
  unfold rationalQuaternionL1
  positivity

/-- Original `rationalQuaternionCast_norm_le_L1` guarantee for the `TransferredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem rationalQuaternionCast_norm_le_L1 (q : Quaternion ℚ) :
    ‖rationalQuaternionCast q‖ ≤ (rationalQuaternionL1 q : ℝ) := by
  simpa [rationalQuaternionL1,Rat.cast_add,Rat.cast_abs,rationalQuaternionCast]
    using quaternion_norm_le_l1 (rationalQuaternionCast q)

/-- Original `transferredGaugeArtifactField_contDiff` guarantee for the `TransferredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem transferredGaugeArtifactField_contDiff (artifact : TransferredGaugeArtifact) :
    ContDiff ℝ ∞ (transferredGaugeArtifactField artifact) :=
  contDiff_const.mul (gaugeFourierArtifactField_contDiff artifact.base)

/-- Original `transferredGaugeArtifactField_periodic` guarantee for the `TransferredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem transferredGaugeArtifactField_periodic (artifact : TransferredGaugeArtifact) :
    IsPeriodicField (transferredGaugeArtifactField artifact) := by
  intro X n
  simp only [transferredGaugeArtifactField,gaugeFourierArtifactField_periodic artifact.base X n]

/-- Original `transferredGaugeArtifactValue_error` guarantee for the `TransferredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem transferredGaugeArtifactValue_error (artifact : TransferredGaugeArtifact)
    (X : Fin 3 → ℚ) (accuracy : ℚ) (ha : 0<accuracy) :
    ‖rationalQuaternionCast (transferredGaugeArtifactValue artifact X accuracy)-
      transferredGaugeArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  let S := rationalQuaternionL1 artifact.transition
  have hS : 0 ≤ S := rationalQuaternionL1_nonneg artifact.transition
  have hden : 0<S+1 := by positivity
  have ht : 0<accuracy/(S+1) := div_pos ha hden
  have herr := gaugeFourierArtifactValue_error artifact.base X (accuracy/(S+1)) ht
  have hnorm := rationalQuaternionCast_norm_le_L1 artifact.transition
  have hSR : (0 : ℝ) ≤ (S : ℝ) := Rat.cast_nonneg.mpr hS
  have hbudget : S*(accuracy/(S+1)) ≤ accuracy := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hbudgetR : (S : ℝ)*((accuracy/(S+1) : ℚ) : ℝ) ≤ (accuracy : ℝ) := by
    exact_mod_cast hbudget
  change ‖rationalQuaternionCast (artifact.transition*gaugeFourierArtifactValue artifact.base X (accuracy/(S+1)))-
    rationalQuaternionCast artifact.transition*gaugeFourierArtifactField artifact.base (rationalSpatialPoint X)‖ ≤ _
  rw [map_mul,← mul_sub,norm_mul]
  have hprod := mul_le_mul hnorm herr (norm_nonneg _) hSR
  exact hprod.trans (by nlinarith)

end
end Qatlib.Concepts.EffectiveGauge.SpectralH1
