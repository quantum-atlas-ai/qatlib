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
namespace Qatlib.Papers.QuatLift26.Boundary
open Set Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier
open scoped Quaternion ContDiff

/-- OQ #139 extension: the same open mean cell of width 3/4 and the same origin value remove the integer and constant freedom. This is not the paper maximum-component selector or a full bit-time theorem. -/
theorem positive_margin_cell_origin_unique
    (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q r : QuaternionField) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (huq : ∀ x, ‖q x‖=1) (hur : ∀ x, ‖r x‖=1)
    (hpq : IsPeriodicField q) (hpr : IsPeriodicField r)
    (hhq : ∀ x, hopf (q x)=spinOfVector (v x))
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x))
    (hsq : IsSolenoidal q) (hsr : IsSolenoidal r) (shift : Fin 3 → ℝ)
    (hmq : ∀ j, shift j+1/8<physicalCubeMean (fun x => connection q x j) ∧
      physicalCubeMean (fun x => connection q x j)<shift j+7/8)
    (hmr : ∀ j, shift j+1/8<physicalCubeMean (fun x => connection r x j) ∧
      physicalCubeMean (fun x => connection r x j)<shift j+7/8)
    (h0 : r 0=q 0) : r=q := by
  exact Qatlib.Concepts.EffectiveGauge.HopfAtlas.sameSource_solenoidal_eq_of_mean_cell_origin v hv q r hq hr huq hur hpq hpr hhq hhr hsq hsr shift hmq hmr h0

end Qatlib.Papers.QuatLift26.Boundary
