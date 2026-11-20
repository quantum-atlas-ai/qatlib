/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceMoment

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact all-order physical rescaling of the original coordinate derivatives -/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- If `f` is smooth, precomposing it with uniform spatial scaling by `length` multiplies its word
derivative at the scaled point by `length^w.length`. -/
theorem spatialWordPartial_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (length : ℝ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => f (length • x)) w=
      fun x => length^w.length • spatialWordPartial f w (length • x) := by
  induction w with
  | nil => funext x; simp only [spatialWordPartial,List.length_nil,pow_zero,one_smul]
  | cons i w ih =>
    funext x
    simp only [spatialWordPartial,ih,List.length_cons]
    have hc := contDiff_spatialWordPartial f hf w
    have hd := ((hc.differentiable (by simp) (length • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul length)).const_smul (length^w.length)
    change HasFDerivAt (fun y => length^w.length • spatialWordPartial f w (length • y)) _ x at hd
    rw [hd.fderiv]
    simp [smul_smul,pow_succ]

/-- For a smooth source, the normalized coordinate spin has a word derivative equal to the source
derivative at the corresponding physical point multiplied by one physical period factor per
derivative. -/
theorem unitCoordinateSpin_word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin 3)) :
    spatialWordPartial (unitCoordinateSpin v) w=
      fun u => physicalPeriod^w.length • spatialWordPartial v w (physicalPeriod • u) :=
  spatialWordPartial_scale v hv physicalPeriod w

/-- Scaling keeps the same physical target and retains all r factors of L. -/
theorem unitCoordinateSpin_word_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin 3)) (u : SpatialPoint) (M : ℝ) (hM : 0 ≤ M)
    (hb : ‖spatialWordPartial v w (physicalPeriod • u)‖ ≤ M) :
    ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤ (7 : ℝ)^w.length*M := by
  rw [unitCoordinateSpin_word v hv,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg physicalPeriod_pos.le _)]
  have hp : physicalPeriod ≤ 7 := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have hpw : physicalPeriod^w.length ≤ (7 : ℝ)^w.length := by
    gcongr
    exact physicalPeriod_pos.le
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg physicalPeriod_pos.le _)).trans
    (mul_le_mul_of_nonneg_right hpw hM)

/-- Unit-coordinate word bounds are derived from the original physical
multi-index program. No normalized moduli are extra input assumptions. -/
theorem OriginalPositiveJetBounds.unit_word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (w : List (Fin 3)) (hw : w≠[]) (u : SpatialPoint) (hu : InUnitCube u) :
    ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤
      (7 : ℝ)^w.length*(bounds w.length : ℝ) := by
  have hphys := hb.word v hv bounds w hw (physicalPeriod • u) (unitCube_scale_physical u hu)
  exact unitCoordinateSpin_word_bound v hv w u _ ((norm_nonneg _).trans hphys) hphys

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
