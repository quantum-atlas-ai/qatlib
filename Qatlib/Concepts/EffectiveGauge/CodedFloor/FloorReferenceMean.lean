/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorMeanSign
import Qatlib.Concepts.EffectiveGauge.RationalFlow.ReferenceMeanLiftInvariant

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Reference Mean

Coded Floor constructions for Effective Gauge.
Defines `floorSourceReferenceMean`.
Proves `physicalCubeMean_congr_on_cube`, `floorPeriodicLift_mean`, `floorSourceReferenceMean_eq`.
-/

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `physicalCubeMean_congr_on_cube` guarantee for the `FloorReferenceMean` construction; the complete source hypotheses are retained. -/
theorem physicalCubeMean_congr_on_cube (f g : SpatialPoint → ℝ)
    (he : ∀ X, InFundamentalCube X → f X=g X) : physicalCubeMean f=physicalCubeMean g := by
  unfold physicalCubeMean
  congr 1
  unfold physicalCubeIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  apply he
  intro i
  exact ⟨hx.1 i,hx.2 i⟩

/-- Original `floorPeriodicLift_mean` guarantee for the `FloorReferenceMean` construction; the complete source hypotheses are retained. -/
theorem floorPeriodicLift_mean (a : ℝ) :
    physicalCubeMean (fun X => connection (floorPeriodicLift a) X 1)=floorMeanCandidate a := by
  calc
    _ = physicalCubeMean (fun X => -floorSinEnergy a X) := by
      apply physicalCubeMean_congr_on_cube
      intro X hX
      rw [floorPeriodicLift_connection a X hX]
      simp only [ite_true,floorSinEnergy]
    _ = _ := by
      simp only [floorMeanCandidate,physicalCubeMean,physicalCubeIntegral,integral_neg,neg_div]

/-- Definition of floor Source Reference Mean in the Coded Floor construction. -/
def floorSourceReferenceMean (a : ℝ) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate (floorPeriodicSpin a) source) (m1 m2 : ℚ) : ℝ :=
  physicalCubeMean (fun X => connection
    (sourcePeriodicReference (floorPeriodicSpin a) (floorPeriodicSpin_contDiff a)
      (floorPeriodicSpin_norm a) source hs m1 m2 (1/14)) X 1)

/-- This identifies only the actual source-built reference mean. No
identity between the source's ODE reference and the comparison lift is
assumed or needed. All Hopf and boundary premises are global and proved. -/
theorem floorSourceReferenceMean_eq (a : ℝ) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate (floorPeriodicSpin a) source) (m1 m2 : ℚ) :
    floorSourceReferenceMean a source hs m1 m2=floorMeanCandidate a := by
  have h := sourcePeriodicReference_mean_eq_boundary_lift
    (floorPeriodicSpin a) (floorPeriodicSpin_contDiff a) (floorPeriodicSpin_norm a)
    (floorPeriodicSpin_periodic a) source hs m1 m2 (1/14) (by norm_num)
    (closedBall floorFamilyCenter 1) floorFamilyBall_in_cube (1 : ℝ) (by norm_num)
    floorFamilyBall_gap (floorPeriodicSpin_constant_off_ball a) (by norm_num)
    (floorPeriodicLift a) (floorPeriodicLift_contDiff a) (floorPeriodicLift_norm a)
    (floorPeriodicLift_hopf a) (floorPeriodicLift_connection_boundary a) 0 1 (by decide)
  exact h.trans (floorPeriodicLift_mean a)

/-- Exact floor distinguishes zero from every positive family parameter.
This is the analytic predicate to which an encoded program reduction
must still connect; it is not itself a computability impossibility. -/
theorem floorSourceReferenceMean_floor (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/16)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate (floorPeriodicSpin a) source) (m1 m2 : ℚ) :
    ⌊floorSourceReferenceMean a source hs m1 m2⌋=if a=0 then (0 : ℤ) else -1 := by
  rw [floorSourceReferenceMean_eq]
  by_cases hz : a=0
  · subst a
    simp only [ite_true,floorMeanCandidate_floor_zero]
  · rw [if_neg hz]
    exact floorMeanCandidate_floor_of_pos a (lt_of_le_of_ne ha (Ne.symm hz)) ha1

end Qatlib.Concepts.EffectiveGauge.CodedFloor
