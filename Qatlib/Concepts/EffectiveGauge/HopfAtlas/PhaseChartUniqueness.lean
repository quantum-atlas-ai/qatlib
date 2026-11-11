/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeUniqueness
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RescaledLine

set_option backward.isDefEq.respectTransparency false

/-!
# Phase Chart Uniqueness

Hopf Atlas constructions for Effective Gauge.
Defines `HasSeedChartPhase`.
Proves `sameHopf_eq_of_seedChartPhase`, `exactChartSeed_phase`, `rescaledOriginSeed_phase`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The selected complex component is real and has the certified margin. -/
def HasSeedChartPhase (chart : SeedChart) (q : ℍ) : Prop :=
  match chart with
  | .north => q.imI=0 ∧ (1/2 : ℝ)<q.re
  | .south => q.imK=0 ∧ (1/2 : ℝ)<q.imJ

/-- Original `sameHopf_eq_of_seedChartPhase` guarantee for the `PhaseChartUniqueness` construction; the complete source hypotheses are retained. -/
theorem sameHopf_eq_of_seedChartPhase (chart : SeedChart) (q r : ℍ)
    (hq : ‖q‖=1) (hr : ‖r‖=1) (hh : hopf r=hopf q)
    (hpq : HasSeedChartPhase chart q) (hpr : HasSeedChartPhase chart r) : r=q := by
  let c := r*star q
  have hc : c.imJ=0 ∧ c.imK=0 := sameHopf_ratio_components q r hq hr hh
  have hn := (normSq_eq_one_iff c).mpr (sameHopf_ratio_norm q r hq hr)
  have ha : c*q=r := sameHopf_ratio_action q r hq
  have hR := congrArg QuaternionAlgebra.re ha
  have hI := congrArg QuaternionAlgebra.imI ha
  have hJ := congrArg QuaternionAlgebra.imJ ha
  have hK := congrArg QuaternionAlgebra.imK ha
  have hci : c.imI=0 ∧ 0<c.re := by
    cases chart with
    | north =>
      change q.imI=0 ∧ (1/2 : ℝ)<q.re at hpq
      change r.imI=0 ∧ (1/2 : ℝ)<r.re at hpr
      simp [hc.1,hc.2,hpq.1,hpr.1] at hR hI
      have hqpos : 0<q.re := by linarith [hpq.2]
      have hz : c.imI=0 := hI.resolve_right hqpos.ne'
      have hpos : 0<c.re := by
        apply (mul_pos_iff_of_pos_right hqpos).mp
        rw [hR]
        linarith [hpr.2]
      exact ⟨hz,hpos⟩
    | south =>
      change q.imK=0 ∧ (1/2 : ℝ)<q.imJ at hpq
      change r.imK=0 ∧ (1/2 : ℝ)<r.imJ at hpr
      simp [hc.1,hc.2,hpq.1,hpr.1] at hJ hK
      have hqpos : 0<q.imJ := by linarith [hpq.2]
      have hz : c.imI=0 := hK.resolve_right hqpos.ne'
      have hpos : 0<c.re := by
        apply (mul_pos_iff_of_pos_right hqpos).mp
        rw [hJ]
        linarith [hpr.2]
      exact ⟨hz,hpos⟩
  simp [Quaternion.normSq_def',hc.1,hc.2,hci.1] at hn
  have hcr : c.re=1 := hn.resolve_right (by intro hneg; linarith [hci.2])
  have hc1 : c=1 := by ext <;> simp [hcr,hci.1,hc.1,hc.2]
  simpa only [hc1,one_mul] using ha.symm

/-- Original `exactChartSeed_phase` guarantee for the `PhaseChartUniqueness` construction; the complete source hypotheses are retained. -/
theorem exactChartSeed_phase (chart : SeedChart) (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : match chart with
      | .north => -(1/2 : ℝ)<s.imI
      | .south => s.imI<(1/2 : ℝ)) : HasSeedChartPhase chart (exactChartSeed chart s) := by
  have h := (exactChartSeed_spec chart s hr hn hc).2.2
  cases chart with
  | north => exact ⟨rfl,h⟩
  | south => exact ⟨rfl,h⟩

/-- Original `rescaledOriginSeed_phase` guarantee for the `PhaseChartUniqueness` construction; the complete source hypotheses are retained. -/
theorem rescaledOriginSeed_phase (v : SpatialPoint → SpatialPoint) (hu : ∀ x, ‖v x‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) :
    HasSeedChartPhase (chosenOriginChart (rescaledSpinSamples source m1 m2))
      (rescaledOriginSeed v source m1 m2) :=
  exactChartSeed_phase _ _ rfl ((spinOfVector_norm _).trans (hu 0))
    (rescaledOriginChart_valid v source hs m1 m2)

/-- Original `selectedPoissonGauge_unique_chart` guarantee for the `PhaseChartUniqueness` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_unique_chart (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1)
    (hh : ∀ x, hopf (q x)=spinOfVector (v x)) (result : SourceMeanSectorResult)
    (hc : SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection q x j)) result)
    (chart : SeedChart) (hchart : HasSeedChartPhase chart (q 0))
    (r : QuaternionField) (hr : ContDiff ℝ ∞ r) (hur : ∀ x, ‖r x‖=1)
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x)) (hpr : IsPeriodicField r) (hsr : IsSolenoidal r)
    (hrchart : HasSeedChartPhase chart (r 0))
    (hmr : ∀ j, ((result.choices j).shift : ℝ)+1/8<physicalCubeMean (fun x => connection r x j) ∧
      physicalCubeMean (fun x => connection r x j)<((result.choices j).shift : ℝ)+7/8) :
    r=selectedPoissonGauge q hq hp result := by
  apply selectedPoissonGauge_unique v hv q hq hp hu hh result hc r hr hur hhr hpr hsr
    (sameHopf_eq_of_seedChartPhase chart (q 0) (r 0) (hu 0) (hur 0)
      ((hhr 0).trans (hh 0).symm) hchart hrchart) hmr

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
