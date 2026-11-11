/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.StoredGaugeState
import Qatlib.Concepts.EffectiveGauge.RationalFlow.NormalizedGaugeSampling

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Gauge Unit Sampling

Spectral H1 constructions for Effective Gauge.
Defines `StoredGaugeUnitSamplingPlan`, `StoredGaugeUnitSamplingPlan.toPlan`, `materializeStoredGaugeUnitSamplingPlan`.
Proves `materializeStoredGaugeUnitSamplingPlan_output`, `storedSourceGaugeUnitSampling_output`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Data and hypotheses for Stored Gauge Unit Sampling Plan in the Spectral H1 construction. -/
structure StoredGaugeUnitSamplingPlan where
  gauge : StoredGaugeState
  tolerance : ℚ
  periodAccuracy : ℚ
  period : ℚ

/-- Definition of to Plan in the Spectral H1 construction. -/
def StoredGaugeUnitSamplingPlan.toPlan (plan : StoredGaugeUnitSamplingPlan) : GaugeUnitSamplingPlan :=
  ⟨plan.gauge.poisson,plan.tolerance,plan.periodAccuracy,plan.period⟩

/-- Definition of materialize Stored Gauge Unit Sampling Plan in the Spectral H1 construction. -/
def materializeStoredGaugeUnitSamplingPlan (state : StoredGaugeState) (tolerance : ℚ) : StoredGaugeUnitSamplingPlan :=
  let ell := gaugeUnitPeriodAccuracy state.frame.gaugeBounds[1] tolerance
  ⟨state,tolerance,ell,fourierPeriodExecution ell⟩

/-- Definition of materialize Stored Gauge Unit Sampling in the Spectral H1 construction. -/
def materializeStoredGaugeUnitSampling (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : Option StoredGaugeUnitSamplingPlan :=
  (storedSourceGaugeFromPrepared source frame tolerance).map
    (fun state => materializeStoredGaugeUnitSamplingPlan state tolerance)

/-- Definition of stored Source Gauge Unit Sampling in the Spectral H1 construction. -/
def storedSourceGaugeUnitSampling (source : RationalJetSource) (plan : StoredGaugeUnitSamplingPlan)
    (address : Fin 3 → ℚ) : Option (Quaternion ℚ) :=
  storedSourceGaugePhysicalValue source plan.gauge
    (fun j => plan.period*rationalUnitWrap address j) plan.tolerance

/-- Original `materializeStoredGaugeUnitSamplingPlan_output` guarantee for the `StoredGaugeUnitSampling` construction; the complete source hypotheses are retained. -/
theorem materializeStoredGaugeUnitSamplingPlan_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap : ℚ) (r : GeneralPoissonValueState) (hprepared : r.preparation.prepared=prepared) (tolerance : ℚ) :
    (materializeStoredGaugeUnitSamplingPlan
      ⟨storeReferenceFrame source prepared (referenceUnitCollar gap),r⟩ tolerance).toPlan=
      materializeGaugeUnitSamplingPlan gap tolerance r := by
  have hb : (storeReferenceFrame source prepared (referenceUnitCollar gap)).gaugeBounds[1]=
      cachedGaugeWordMajorant (referenceUnitCollar gap) prepared 1 :=
    storeReferenceFrame_gaugeBounds source prepared _ (1 : Fin 4)
  simp [materializeStoredGaugeUnitSamplingPlan,StoredGaugeUnitSamplingPlan.toPlan,
    materializeGaugeUnitSamplingPlan,hprepared,hb]

/-- Original `storedSourceGaugeUnitSampling_output` guarantee for the `StoredGaugeUnitSampling` construction; the complete source hypotheses are retained. -/
theorem storedSourceGaugeUnitSampling_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap : ℚ) (plan : StoredGaugeUnitSamplingPlan)
    (hframe : plan.gauge.frame=storeReferenceFrame source prepared (referenceUnitCollar gap))
    (hprepared : plan.gauge.poisson.preparation.prepared=prepared) (address : Fin 3 → ℚ) :
    storedSourceGaugeUnitSampling source plan address=sourceGaugeUnitSampling source gap plan.toPlan address := by
  unfold storedSourceGaugeUnitSampling sourceGaugeUnitSampling StoredGaugeUnitSamplingPlan.toPlan
  have he : plan.gauge=⟨storeReferenceFrame source prepared (referenceUnitCollar gap),plan.gauge.poisson⟩ := by
    rw [← hframe]
  rw [he]
  exact storedSourceGaugePhysicalValue_store source prepared gap _ hprepared _ _

end Qatlib.Concepts.EffectiveGauge.SpectralH1
