/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Reference Mean Lift Invariant

Rational Flow constructions for Effective Gauge.
Proves `sourcePeriodicReference_mean_eq_boundary_lift`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Only the mean is identified. The competing boundary-flat lift need
not equal the actual source reference, so no hidden ODE identity is used. -/
theorem sourcePeriodicReference_mean_eq_boundary_lift (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hqu : ∀ x, ‖q x‖=1)
    (hhopf : ∀ x, hopf (q x)=spinOfVector (v x))
    (hboundary : ∀ x, OnCubeBoundary x → ∀ k, connection q x k=0)
    (i j : Fin 3) (hij : i≠j) :
    physicalCubeMean (fun x => connection (sourcePeriodicReference v hv hu source hs m1 m2 eta) x j)=
      physicalCubeMean (fun x => connection q x j) := by
  calc
    _ = -physicalCubeMean (fun x => x i*sourceCurvature v x i j) :=
      sourcePeriodicReference_mean v hv hu hp source hs m1 m2 eta he B hB mu hm hg hoff hmargin i j hij
    _ = -physicalCubeMean (fun x => x i*connectionCurvature q x i j) := by
      apply congrArg Neg.neg
      apply congrArg physicalCubeMean
      funext x
      rw [connectionCurvature_eq_source v hv q hq hqu hhopf x i j]
    _ = _ := (physicalCubeMean_connection_curvature q hq hboundary i j hij).symm

end Qatlib.Concepts.EffectiveGauge.RationalFlow
