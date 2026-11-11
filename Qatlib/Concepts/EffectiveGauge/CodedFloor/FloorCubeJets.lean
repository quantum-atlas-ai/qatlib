/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorBumpFamily
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordCubeClosure
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Cube Jets

Coded Floor constructions for Effective Gauge.
Proves `spatialWordPartial_eq_on_closedPhysicalCube`, `floorPeriodicLift_word_eq_raw`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Equality on the physical closed cube transfers true coordinate jets,
including upper faces. This is an analytic identity, not a floor evaluator. -/
theorem spatialWordPartial_eq_on_closedPhysicalCube {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (he : ∀ X, InFundamentalCube X → f X=g X) (w : List (Fin 3))
    (X : SpatialPoint) (hX : InFundamentalCube X) : spatialWordPartial f w X=spatialWordPartial g w X := by
  let F := fun u => f (physicalPeriod • u)
  let G := fun u => g (physicalPeriod • u)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_id.const_smul physicalPeriod)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_id.const_smul physicalPeriod)
  have hunit (u : SpatialPoint) (hu : InUnitCube u) : F u=G u := by
    apply he
    intro i
    change 0 ≤ physicalPeriod*u i ∧ physicalPeriod*u i ≤ physicalPeriod
    exact ⟨mul_nonneg physicalPeriod_pos.le (hu i).1,
      (mul_le_mul_of_nonneg_left (hu i).2 physicalPeriod_pos.le).trans_eq (mul_one _)⟩
  have hxunit : InUnitCube (physicalPeriod⁻¹ • X) := by
    intro i
    change 0 ≤ physicalPeriod⁻¹*X i ∧ physicalPeriod⁻¹*X i ≤ 1
    refine ⟨mul_nonneg (inv_pos.mpr physicalPeriod_pos).le (hX i).1,?_⟩
    exact (mul_le_mul_of_nonneg_left (hX i).2 (inv_pos.mpr physicalPeriod_pos).le).trans_eq
      (inv_mul_cancel₀ physicalPeriod_pos.ne')
  have hword := spatialWordPartial_eq_on_closedUnitCube F G hF hG hunit w (physicalPeriod⁻¹ • X) hxunit
  change spatialWordPartial (fun u => f (physicalPeriod • u)) w (physicalPeriod⁻¹ • X)=
    spatialWordPartial (fun u => g (physicalPeriod • u)) w (physicalPeriod⁻¹ • X) at hword
  rw [spatialWordPartial_scale f hf physicalPeriod w,spatialWordPartial_scale g hg physicalPeriod w] at hword
  simp only [smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul] at hword
  have h := congrArg (fun value : E => (physicalPeriod^w.length)⁻¹ • value) hword
  simpa only [smul_smul,inv_mul_cancel₀ (pow_ne_zero w.length physicalPeriod_pos.ne'),one_smul] using h

/-- Original `floorPeriodicLift_word_eq_raw` guarantee for the `FloorCubeJets` construction; the complete source hypotheses are retained. -/
theorem floorPeriodicLift_word_eq_raw (a : ℝ) (w : List (Fin 3))
    (X : SpatialPoint) (hX : InFundamentalCube X) :
    spatialWordPartial (floorPeriodicLift a) w X=spatialWordPartial (floorRawLift a) w X :=
  spatialWordPartial_eq_on_closedPhysicalCube _ _ (floorPeriodicLift_contDiff a) (contDiff_floorRawLift a)
    (floorPeriodicLift_eq_raw_on_cube a) w X hX

end Qatlib.Concepts.EffectiveGauge.CodedFloor
