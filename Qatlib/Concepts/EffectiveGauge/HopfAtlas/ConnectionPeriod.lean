/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Connection Period

Hopf Atlas constructions for Effective Gauge.
Proves `physicalLoopIntegral_partial_periodic`, `poissonCorrectedLift_connection_period`, `selectedPoissonGauge_connection_period`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- A real periodic phase has zero increment around every coordinate loop. -/
theorem physicalLoopIntegral_partial_periodic (f : SpatialPoint → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f) (j : Fin 3) (x : SpatialPoint) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      fderiv ℝ f (x+t • EuclideanSpace.single j 1) (EuclideanSpace.single j 1))=0 := by
  let e : SpatialPoint := EuclideanSpace.single j 1
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (x+s • e))
      (fderiv ℝ f (x+t • e) e) t := by
    apply ((hf.differentiable (by simp) (x+t • e)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const e |>.const_add x)).congr_deriv
    simp only [one_smul]
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (x+t • e) e)
      volume 0 physicalPeriod :=
    ((((hf.fderiv_right (m := ∞) (by rfl)).continuous).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).intervalIntegrable _ _
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  have hl : physicalPeriod • e=latticeShift (Pi.single j 1) := by
    ext k
    simp [e,latticeShift,Pi.single_apply]
  change (∫ t in (0 : ℝ)..physicalPeriod, fderiv ℝ f (x+t • e) e)=0
  rw [hft,hl,hp x (Pi.single j 1)]
  simp

/-- Original `poissonCorrectedLift_connection_period` guarantee for the `ConnectionPeriod` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_connection_period (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (j : Fin 3) (x : SpatialPoint) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      connection (poissonCorrectedLift q hq hp) (x+t • EuclideanSpace.single j 1) j)=
      ∫ t in (0 : ℝ)..physicalPeriod, connection q (x+t • EuclideanSpace.single j 1) j := by
  let theta := physicalPoissonPhase q hq hp
  have ht := physicalPoissonPhase_contDiff q hq hp
  have heq (t : ℝ) : connection (poissonCorrectedLift q hq hp) (x+t • EuclideanSpace.single j 1) j=
      connection q (x+t • EuclideanSpace.single j 1) j+
        fderiv ℝ theta (x+t • EuclideanSpace.single j 1) (EuclideanSpace.single j 1) :=
    connection_gauge_unit (hq.differentiable (by simp) _) (ht.differentiable (by simp) _) (hu _) j
  simp_rw [heq]
  have hline : Continuous (fun t : ℝ => x+t • EuclideanSpace.single j 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hiA : IntervalIntegrable (fun t : ℝ => connection q (x+t • EuclideanSpace.single j 1) j)
      volume 0 physicalPeriod :=
    ((contDiff_connection q hq j).continuous.comp hline).intervalIntegrable _ _
  have hiT : IntervalIntegrable (fun t : ℝ =>
      fderiv ℝ theta (x+t • EuclideanSpace.single j 1) (EuclideanSpace.single j 1))
      volume 0 physicalPeriod :=
    (((ht.fderiv_right (m := ∞) (by rfl)).continuous.comp hline).clm_apply
      (g := fun _ : ℝ => EuclideanSpace.single j 1) continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hiA hiT,
    physicalLoopIntegral_partial_periodic theta ht (physicalPoissonPhase_periodic q hq hp),add_zero]

/-- Original `selectedPoissonGauge_connection_period` guarantee for the `ConnectionPeriod` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_connection_period (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult)
    (j : Fin 3) (x : SpatialPoint) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      connection (selectedPoissonGauge q hq hp result) (x+t • EuclideanSpace.single j 1) j)=
      (∫ t in (0 : ℝ)..physicalPeriod, connection q (x+t • EuclideanSpace.single j 1) j)+
        physicalPeriod*((result.choices j).winding : ℝ) := by
  rw [selectedPoissonGauge,integerGauge_connection_period _ (poissonCorrectedLift_contDiff q hq hp)
    (poissonCorrectedLift_norm q hq hp hu),poissonCorrectedLift_connection_period q hq hp hu]
  rfl

/-- Original `coordinateEdge_on_boundary` guarantee for the `ConnectionPeriod` construction; the complete source hypotheses are retained. -/
theorem coordinateEdge_on_boundary (j : Fin 3) (t : ℝ) (ht : t∈Icc 0 physicalPeriod) :
    OnCubeBoundary (t • EuclideanSpace.single j 1) := by
  constructor
  · intro k
    by_cases h : k=j
    · subst k; simpa using ht
    · simpa [PiLp.single_apply,h] using And.intro (le_refl (0 : ℝ)) physicalPeriod_pos.le
  · have hk : ∃ k : Fin 3, k≠j := by fin_cases j <;> decide
    obtain ⟨k,hk⟩ := hk
    exact ⟨k,Or.inl (by simp [hk])⟩

/-- Original `sourcePeriodicReference_connection_period` guarantee for the `ConnectionPeriod` construction; the complete source hypotheses are retained. -/
theorem sourcePeriodicReference_connection_period (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ x ∈ B, InFundamentalCube x) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ x ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖x-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (j : Fin 3) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      connection (sourcePeriodicReference v hv hu source hs m1 m2 eta)
        (t • EuclideanSpace.single j 1) j)=0 := by
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  have hseed := rescaledOriginSeed_spec v hu source hs m1 m2
  have heR : 0<(eta : ℝ) := by exact_mod_cast he
  calc
    _ = ∫ _t in (0 : ℝ)..physicalPeriod, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hb := coordinateEdge_on_boundary j t (by simpa [uIcc_of_le physicalPeriod_pos.le] using ht)
      exact periodicReference_connection_boundary_zero v hv hu _ hseed.1 (spin_field_periodic hp)
        _ (mul_pos physicalPeriod_pos heR) _ hc hseed.2.1 _ hb j
    _ = 0 := by simp

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
