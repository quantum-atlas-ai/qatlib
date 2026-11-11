/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicIntegral
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicExtension

set_option backward.isDefEq.respectTransparency false

/-! # Periodic coordinate words and global bounds without differentiating wrapping -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `periodicField_spatialWordPartial` guarantee for the `WordPeriodic` construction; the complete source hypotheses are retained. -/
theorem periodicField_spatialWordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f) (w : List (Fin 3)) :
    IsPeriodicField (spatialWordPartial f w) := by
  induction w with
  | nil => exact hp
  | cons i w ih =>
    have hd := periodicField_fderiv (spatialWordPartial f w) (contDiff_spatialWordPartial f hf w) ih
    intro x n
    simp only [spatialWordPartial]
    rw [hd x n]

/-- Only the already differentiated periodic field is evaluated at a wrapped
point. The discontinuous wrapping operation is never differentiated. -/
theorem normalizedPeriodicWordBound_global {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f)
    (w : List (Fin 3)) (M : ℝ)
    (hb : ∀ u, InUnitCube u → ‖spatialWordPartial (fun y => f (physicalPeriod • y)) w u‖ ≤ M)
    (x : SpatialPoint) : ‖spatialWordPartial (fun y => f (physicalPeriod • y)) w x‖ ≤ M := by
  let X := physicalPeriod • x
  let u := physicalPeriod⁻¹ • wrapPoint X
  have hu : InUnitCube u := by
    intro i
    have hi := wrapPoint_cube X i
    change 0≤physicalPeriod⁻¹*wrapPoint X i ∧ physicalPeriod⁻¹*wrapPoint X i≤1
    constructor
    · exact mul_nonneg (inv_nonneg.mpr physicalPeriod_pos.le) hi.1
    · calc
        _ ≤ physicalPeriod⁻¹*physicalPeriod := mul_le_mul_of_nonneg_left hi.2 (inv_nonneg.mpr physicalPeriod_pos.le)
        _ = 1 := inv_mul_cancel₀ physicalPeriod_pos.ne'
  have hXu : physicalPeriod • u=wrapPoint X := by
    simp only [u,smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul]
  have hper := periodicField_spatialWordPartial f hf hp w X (fun i => -⌊X i/physicalPeriod⌋)
  rw [← wrapPoint_shift X] at hper
  have heq : spatialWordPartial (fun y => f (physicalPeriod • y)) w x=
      spatialWordPartial (fun y => f (physicalPeriod • y)) w u := by
    simp only [spatialWordPartial_scale f hf,hXu,hper]
    rfl
  rw [heq]
  exact hb u hu

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
