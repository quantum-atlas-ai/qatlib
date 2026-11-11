/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeUniqueness

set_option backward.isDefEq.respectTransparency false

/-! Fixed OQ #139@6c330d5a2ea87d31e23d988d91a433eae284e422, preserving author history.
These are explicitly scoped consumers, not a whole-paper coverage or rank claim. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QuatLift26.Gauge
open Set Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier
open scoped Quaternion ContDiff

/-- Formal comparison with Supplement Lemma 5: complete smooth periodic unit fields and integer/constant left-phase freedom. This is not an effective selector or acceptance of the full published gauge algorithm. -/
theorem same_spin_solenoidal_integer_phase
    (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q r : QuaternionField) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (huq : ∀ x, ‖q x‖=1) (hur : ∀ x, ‖r x‖=1)
    (hpq : IsPeriodicField q) (hpr : IsPeriodicField r)
    (hhq : ∀ x, hopf (q x)=spinOfVector (v x))
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x))
    (hsq : IsSolenoidal q) (hsr : IsSolenoidal r) :
    ∃ n : SpatialFrequency,
      (∀ x j, connection r x j=connection q x j+(n j : ℝ)) ∧
      (∀ x, r x=phase (windingLinear n x)*(r 0*star (q 0))*q x) := by
  exact Qatlib.Concepts.EffectiveGauge.HopfAtlas.sameSource_solenoidal_classification v hv q r hq hr huq hur hpq hpr hhq hhr hsq hsr

end Qatlib.Papers.QuatLift26.Gauge
