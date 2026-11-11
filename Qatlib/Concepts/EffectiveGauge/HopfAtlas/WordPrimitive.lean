/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordIntegral
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordAffine
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz

set_option backward.isDefEq.respectTransparency false

/-! # Pure-transverse derivatives of an actual coordinate primitive -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `coordinateFace_comp` guarantee for the `WordPrimitive` construction; the complete source hypotheses are retained. -/
theorem coordinateFace_comp (j : Fin 3) (a b : ℝ) (x : SpatialPoint) :
    coordinateFace j a (coordinateFace j b x)=coordinateFace j a x := by
  ext i
  by_cases hi : i=j
  · subst i
    rw [coordinateFace_same,coordinateFace_same]
  · rw [coordinateFace_other j i a _ hi,coordinateFace_other j i b _ hi,
      coordinateFace_other j i a _ hi]

/-- Original `coordinateFace_at_coordinate` guarantee for the `WordPrimitive` construction; the complete source hypotheses are retained. -/
theorem coordinateFace_at_coordinate (j : Fin 3) (x : SpatialPoint) :
    coordinateFace j (x j) x=x := by simp [coordinateFace]

/-- Definition of coordinate Primitive in the Hopf Atlas construction. -/
def coordinatePrimitive (gamma : SpatialPoint → ℝ) (x : SpatialPoint) : ℝ :=
  ∫ s in (0 : ℝ)..x 1, gamma (coordinateFace 1 s x)

/-- Definition of coordinate Primitive Source in the Hopf Atlas construction. -/
def coordinatePrimitiveSource (gamma : SpatialPoint → ℝ) (p : SpatialPoint × ℝ) : ℝ :=
  (p.1 1/physicalPeriod)*gamma (coordinateFace 1 ((p.1 1/physicalPeriod)*p.2) p.1)

/-- Original `contDiff_coordinatePrimitiveSource` guarantee for the `WordPrimitive` construction; the complete source hypotheses are retained. -/
theorem contDiff_coordinatePrimitiveSource (gamma : SpatialPoint → ℝ) (hg : ContDiff ℝ ∞ gamma) :
    ContDiff ℝ ∞ (coordinatePrimitiveSource gamma) := by
  have hy : ContDiff ℝ ∞ (fun p : SpatialPoint × ℝ => p.1 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : SpatialPoint →L[ℝ] ℝ).contDiff.comp contDiff_fst
  have ha : ContDiff ℝ ∞ (fun p : SpatialPoint × ℝ => p.1 1/physicalPeriod) := hy.div_const _
  have hf : ContDiff ℝ ∞ (fun p : SpatialPoint × ℝ =>
      coordinateFace 1 ((p.1 1/physicalPeriod)*p.2) p.1) :=
    contDiff_fst.add (((ha.mul contDiff_snd).sub hy).smul contDiff_const)
  exact ha.mul (hg.comp hf)

/-- Physical path length L and the reciprocal L in the integrand are both
retained. This is the real primitive, with no argument/floor convention. -/
theorem coordinatePrimitive_eq_physical_integral (gamma : SpatialPoint → ℝ) (x : SpatialPoint) :
    coordinatePrimitive gamma x=
      ∫ t in (0 : ℝ)..physicalPeriod, coordinatePrimitiveSource gamma (x,t) := by
  have h := smul_integral_comp_mul_left (a := (0 : ℝ)) (b := physicalPeriod)
    (fun s => gamma (coordinateFace 1 s x)) (x 1/physicalPeriod)
  rw [mul_zero,div_mul_cancel₀ _ physicalPeriod_pos.ne',smul_eq_mul] at h
  change _=(∫ t in (0 : ℝ)..physicalPeriod,
    (x 1/physicalPeriod)*gamma (coordinateFace 1 ((x 1/physicalPeriod)*t) x))
  rw [integral_const_mul]
  exact h.symm

/-- Freezing the integration endpoint is legitimate for every word which
contains no integration direction. Only actual coordinate derivatives occur. -/
theorem spatialWordPartial_coordinatePrimitiveSource (gamma : SpatialPoint → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (w : List (Fin 3)) (hw : (1 : Fin 3)∉w)
    (x : SpatialPoint) (t : ℝ) :
    spatialWordPartial (fun y => coordinatePrimitiveSource gamma (y,t)) w x=
      (x 1/physicalPeriod)*spatialWordPartial gamma w
        (coordinateFace 1 ((x 1/physicalPeriod)*t) x) := by
  let f := fun y => coordinatePrimitiveSource gamma (y,t)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_coordinatePrimitiveSource gamma hg).comp (contDiff_id.prodMk contDiff_const)
  have hface := congrFun (spatialWordPartial_coordinateFace f hf 1 (x 1) w) x
  simp only [if_neg hw,coordinateFace_at_coordinate] at hface
  have heq : (fun y => f (coordinateFace 1 (x 1) y))=
      fun y => (x 1/physicalPeriod) • gamma (coordinateFace 1 ((x 1/physicalPeriod)*t) y) := by
    funext y
    dsimp only [f,coordinatePrimitiveSource]
    rw [coordinateFace_same,coordinateFace_comp]
    rfl
  change spatialWordPartial f w x=_
  rw [← hface,heq,spatialWordPartial_const_smul
      (fun y => gamma (coordinateFace 1 ((x 1/physicalPeriod)*t) y))
      (hg.comp (contDiff_coordinateFace 1 ((x 1/physicalPeriod)*t))) (x 1/physicalPeriod) w,
    spatialWordPartial_coordinateFace gamma hg]
  simp only [if_neg hw,smul_eq_mul]

/-- Original `coordinatePrimitive_transverse_word_bound` guarantee for the `WordPrimitive` construction; the complete source hypotheses are retained. -/
theorem coordinatePrimitive_transverse_word_bound (gamma : SpatialPoint → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (w : List (Fin 3)) (hw : (1 : Fin 3)∉w)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ y, InUnitCube y → ‖spatialWordPartial gamma w y‖ ≤ M)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (coordinatePrimitive gamma) w x‖ ≤ M := by
  have heq : coordinatePrimitive gamma=
      fun y => ∫ t in (0 : ℝ)..physicalPeriod, coordinatePrimitiveSource gamma (y,t) :=
    funext (coordinatePrimitive_eq_physical_integral gamma)
  rw [heq]
  have hbound := spatialWordPartial_intervalIntegral_norm_le (coordinatePrimitiveSource gamma)
    (contDiff_coordinatePrimitiveSource gamma hg) w x ((x 1/physicalPeriod)*M) (by
      intro t ht
      rw [spatialWordPartial_coordinatePrimitiveSource gamma hg w hw]
      have hfac : 0 ≤ x 1/physicalPeriod := div_nonneg (hx 1).1 physicalPeriod_pos.le
      have hpoint : InUnitCube (coordinateFace 1 ((x 1/physicalPeriod)*t) x) := by
        intro i
        by_cases hi : i=1
        · subst i
          rw [coordinateFace_same]
          constructor
          · exact mul_nonneg hfac ht.1
          · calc
              _ ≤ (x 1/physicalPeriod)*physicalPeriod := mul_le_mul_of_nonneg_left ht.2 hfac
              _ = x 1 := div_mul_cancel₀ _ physicalPeriod_pos.ne'
              _ ≤ 1 := (hx 1).2
        · rw [coordinateFace_other _ _ _ _ hi]
          exact hx i
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hfac]
      exact mul_le_mul_of_nonneg_left (hb _ hpoint) hfac)
  have hc : physicalPeriod*((x 1/physicalPeriod)*M)=x 1*M := by
    field_simp [physicalPeriod_pos.ne']
  rw [hc] at hbound
  exact hbound.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hx 1).2 hM)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
