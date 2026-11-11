/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

/-! # Actual parameter-word derivatives commute with the physical interval integral -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration of a continuous path is a bounded real-linear map. -/
def integrateWordPath [CompleteSpace E] : C(TransportTime,E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0 : ℝ)..physicalPeriod, extendPath f t
      map_add' := by
        intro f g
        exact integral_add ((continuous_extendPath f).intervalIntegrable _ _)
          ((continuous_extendPath g).intervalIntegrable _ _)
      map_smul' := by intro c f; exact integral_smul c (extendPath f) }
    physicalPeriod (by
      intro f
      calc
        _ ≤ ‖f‖*|physicalPeriod-0| := norm_integral_le_of_norm_le_const
          (fun t _ => f.norm_coe_le_norm _)
        _ = physicalPeriod*‖f‖ := by rw [sub_zero,abs_of_pos physicalPeriod_pos]; ring)

/-- Original `spatialWordPartial_sourcePathOver_eval` guarantee for the `WordIntegral` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_sourcePathOver_eval (g : SpatialPoint × ℝ → E)
    (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) (x : SpatialPoint) (t : TransportTime) :
    spatialWordPartial (sourcePathOver g hg.continuous) w x t=
      spatialWordPartial (fun y => g (y,(t : ℝ))) w x := by
  have h := congrFun (spatialWordPartial_clm (ContinuousMap.evalCLM ℝ t)
    (sourcePathOver g hg.continuous) (contDiff_sourcePathOver hg) w) x
  exact h.symm

/-- Original `spatialWordPartial_intervalIntegral` guarantee for the `WordIntegral` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_intervalIntegral [CompleteSpace E] (g : SpatialPoint × ℝ → E)
    (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) (x : SpatialPoint) :
    spatialWordPartial (fun y => ∫ t in (0 : ℝ)..physicalPeriod, g (y,t)) w x=
      ∫ t in (0 : ℝ)..physicalPeriod, spatialWordPartial (fun y => g (y,t)) w x := by
  have heq : (fun y => ∫ t in (0 : ℝ)..physicalPeriod, g (y,t))=
      fun y => integrateWordPath (sourcePathOver g hg.continuous y) := by
    funext y
    change (∫ t in (0 : ℝ)..physicalPeriod, g (y,t))=
      ∫ t in (0 : ℝ)..physicalPeriod, extendPath (sourcePathOver g hg.continuous y) t
    apply integral_congr
    intro t ht
    rw [uIcc_of_le physicalPeriod_pos.le] at ht
    rw [extendPath_on _ t ht]
    rfl
  rw [heq,spatialWordPartial_clm _ _ (contDiff_sourcePathOver hg)]
  change (∫ t in (0 : ℝ)..physicalPeriod,
    extendPath (spatialWordPartial (sourcePathOver g hg.continuous) w x) t)=_
  apply integral_congr
  intro t ht
  rw [uIcc_of_le physicalPeriod_pos.le] at ht
  rw [extendPath_on _ t ht]
  exact spatialWordPartial_sourcePathOver_eval g hg w x ⟨t,ht⟩

/-- This bound concerns the actual Bochner integral and actual derivatives,
not a supplied regularity certificate for an unknown reference. -/
theorem spatialWordPartial_intervalIntegral_norm_le [CompleteSpace E] (g : SpatialPoint × ℝ → E)
    (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) (x : SpatialPoint) (M : ℝ)
    (hb : ∀ t ∈ Icc 0 physicalPeriod, ‖spatialWordPartial (fun y => g (y,t)) w x‖ ≤ M) :
    ‖spatialWordPartial (fun y => ∫ t in (0 : ℝ)..physicalPeriod, g (y,t)) w x‖ ≤
      physicalPeriod*M := by
  rw [spatialWordPartial_intervalIntegral g hg]
  calc
    _ ≤ M*|physicalPeriod-0| := norm_integral_le_of_norm_le_const (fun t ht => by
      rw [uIoc_of_le physicalPeriod_pos.le] at ht
      exact hb t ⟨ht.1.le,ht.2⟩)
    _ = _ := by rw [sub_zero,abs_of_pos physicalPeriod_pos]; ring

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
