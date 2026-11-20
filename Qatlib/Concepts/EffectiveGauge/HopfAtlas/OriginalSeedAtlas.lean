/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.EffectiveSeedTransition
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Original Seed Atlas

Hopf Atlas constructions for Effective Gauge.
Defines `originalSeedChartAccepted`, `originalSeedTransitionRun`.
Proves `originalSeedTransitionRun_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of original Seed Chart Accepted in the Hopf Atlas construction. -/
def originalSeedChartAccepted (source : RationalJetSource) (m1 m2 : ℚ) (chart : SeedChart) : Bool :=
  seedChartAccepted (originSpinSamples (rescaledSpinSamples (originalFirstJetPair source 0) m1 m2) 4) chart

/-- Definition of original Seed Transition Run in the Hopf Atlas construction. -/
def originalSeedTransitionRun (source : RationalJetSource) (m1 m2 : ℚ)
    (fromChart toChart : SeedChart) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  rationalSeedTransitionRun (originalFirstJetPair source 0) m1 m2 fromChart toChart tolerance

noncomputable section
open scoped Quaternion

/-- For a unit field with accurate rational jets, two charts accepted by the original sample
procedure admit a rational origin transition within `tolerance / 2` of the exact transition
whenever `tolerance > 0`. -/
theorem originalSeedTransitionRun_correct (v : SpatialPoint → SpatialPoint) (hu : ∀ x, ‖v x‖=1)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (m1 m2 : ℚ) (a b : SeedChart)
    (ha : originalSeedChartAccepted source m1 m2 a=true)
    (hb : originalSeedChartAccepted source m1 m2 b=true)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ value, originalSeedTransitionRun source m1 m2 a b tolerance=some value ∧
      ‖rationalQuaternionCast value-seedChartTransition a b (sourceQuaternion v 0)‖ ≤ (tolerance : ℝ)/2 :=
  rationalSeedTransitionRun_correct v hu (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    m1 m2 a b ha hb tolerance ht

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
