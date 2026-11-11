/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpatialLipschitz
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonAddress
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Poisson Phase Value Error

Torus Fourier constructions for Effective Gauge.
Proves `generalPoissonPhysicalPhaseValue_error`.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `generalPoissonPhysicalPhaseValue_error` guarantee for the `PhysicalPoissonPhaseValueError` construction; the complete source hypotheses are retained. -/
theorem generalPoissonPhysicalPhaseValue_error (r : GeneralPoissonValueState)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (hC6 : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤
        (r.preparation.referenceCache.connectionBounds[6] : ℝ))
    (tau : ℚ) (hvalue : ∀ a : Fin 3 → ℚ,
      |(generalPoissonStateValue r a : ℝ)-normalizedConnectionPoisson q hq hp (rationalSpatialPoint a)| ≤ (tau : ℝ)/2)
    (X : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    |(generalPoissonPhysicalPhaseValue r X tolerance : ℝ)-
      physicalPoissonPhase q hq hp (rationalSpatialPoint X)| ≤ (tau : ℝ)+(tolerance : ℝ)/30 := by
  let C6 := r.preparation.referenceCache.connectionBounds[6]
  let ell := physicalPoissonAddressAccuracy C6 X tolerance
  let a := rationalPhysicalPoissonAddress X ell
  let x := rationalSpatialPoint a
  let y := physicalPeriod⁻¹ • rationalSpatialPoint X
  let chi := normalizedConnectionPoisson q hq hp
  let D : ℝ := 156*|(C6 : ℝ)|
  let S : ℝ := rationalAddressMagnitude X
  have hD : 0 ≤ D := by positivity
  have hpartial (z : SpatialPoint) (j : Fin 3) :
      |fderiv ℝ chi z (EuclideanSpace.single j 1)| ≤ D := by
    have h := normalizedConnectionPoisson_word_bound q hq hp (C6 : ℝ) hC6 [j] (by simp) z
    change ‖fderiv ℝ chi z (EuclideanSpace.single j 1)‖ ≤ 156*(C6 : ℝ) at h
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
  have hcoord (j : Fin 3) : |x j-y j| ≤ |(X j : ℝ)| * (ell : ℝ)/30 :=
    rationalPhysicalPoissonAddress_error C6 X tolerance ht j
  have hS : S=|(X 0 : ℝ)|+|(X 1 : ℝ)|+|(X 2 : ℝ)| := by
    simp only [S,rationalAddressMagnitude,Fin.sum_univ_three,Rat.cast_add,Rat.cast_abs]
  have hsum : |x 0-y 0|+|x 1-y 1|+|x 2-y 2| ≤ S*(ell : ℝ)/30 := by
    rw [hS]
    linarith [hcoord 0,hcoord 1,hcoord 2]
  have hbudget : D*S*(ell : ℝ) ≤ (tolerance : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (physicalPoissonAddressAccuracy_budget C6 X tolerance ht)
    push_cast at h
    exact h
  have hdist : |chi x-chi y| ≤ (tolerance : ℝ)/30 := by
    have hglobal := spatial_partial_lipschitz chi (normalizedConnectionPoisson_spec q hq hp).1 D hD hpartial x y
    have h := hglobal.trans (mul_le_mul_of_nonneg_left hsum hD)
    nlinarith
  have hpoint := hvalue a
  have hzero := hvalue 0
  have hzeroPoint : rationalSpatialPoint (0 : Fin 3 → ℚ)=0 := by ext j; simp [rationalSpatialPoint]
  rw [hzeroPoint] at hzero
  change |((generalPoissonStateValue r a-generalPoissonStateValue r 0 : ℚ) : ℝ)-(chi y-chi 0)| ≤ _
  rw [Rat.cast_sub]
  have hid : (generalPoissonStateValue r a : ℝ)-(generalPoissonStateValue r 0 : ℝ)-(chi y-chi 0)=
      ((generalPoissonStateValue r a : ℝ)-chi x)+(chi x-chi y)-((generalPoissonStateValue r 0 : ℝ)-chi 0) := by ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
