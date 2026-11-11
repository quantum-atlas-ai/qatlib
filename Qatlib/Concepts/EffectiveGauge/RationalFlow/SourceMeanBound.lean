/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceMoment

set_option backward.isDefEq.respectTransparency false

/-!
# Source Mean Bound

Rational Flow constructions for Effective Gauge.
Proves `unitCubeIntegral_abs_le`, `unitSourceMoment_abs_le`, `unitSourceMoment_integral_bound`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `unitCubeIntegral_abs_le` guarantee for the `SourceMeanBound` construction; the complete source hypotheses are retained. -/
theorem unitCubeIntegral_abs_le (f : SpatialPoint → ℝ) (K : ℝ)
    (hbound : ∀ x, InUnitCube x → |f x| ≤ K) : |unitCubeIntegral f| ≤ K := by
  have hvol : volume (Icc (0 : Fin 3 → ℝ) 1)=(1 : ENNReal) := by
    simp [Real.volume_Icc_pi]
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure (Fin 3 → ℝ))) (f := fun u => f (WithLp.toLp 2 u)) (C := K)
    (by rw [hvol]; norm_num : volume (Icc (0 : Fin 3 → ℝ) 1)<(⊤ : ENNReal)) (fun u hu => ?_)
  · simp only [Measure.real,hvol,ENNReal.toReal_one,mul_one] at h
    simpa only [unitCubeIntegral,Real.norm_eq_abs,Pi.one_def] using h
  · rw [Real.norm_eq_abs]
    exact hbound _ (fun i => ⟨hu.1 i,hu.2 i⟩)

/-- Original `unitSourceMoment_abs_le` guarantee for the `SourceMeanBound` construction; the complete source hypotheses are retained. -/
theorem unitSourceMoment_abs_le (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (m1 : ℝ) (hm1 : 0 ≤ m1)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖sourcePhysicalPartial v i x‖ ≤ m1)
    (u : SpatialPoint) (hucube : InUnitCube u) (i j : Fin 3) :
    |sourceCurvatureMoment (unitCoordinateSpin v) i j u| ≤ (7*m1)^2/2 := by
  have hp : physicalPeriod ≤ 7 := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have hu' := unitCube_scale_physical u hucube
  have hd (k : Fin 3) : ‖sourcePhysicalPartial (unitCoordinateSpin v) k u‖ ≤ 7*m1 := by
    rw [sourcePhysicalPartial_unitCoordinateSpin v hv,norm_smul,Real.norm_eq_abs,
      abs_of_pos physicalPeriod_pos]
    exact (mul_le_mul_of_nonneg_left (hb _ hu' k) physicalPeriod_pos.le).trans
      (mul_le_mul_of_nonneg_right hp hm1)
  have hcurv := spinCurvatureValue_abs_le (spinOfVector (unitCoordinateSpin v u))
    (spinOfVector (sourcePhysicalPartial (unitCoordinateSpin v) i u))
    (spinOfVector (sourcePhysicalPartial (unitCoordinateSpin v) j u))
  have hnorm : ‖unitCoordinateSpin v u‖=1 := hu _
  simp only [spinOfVector_norm,hnorm,one_mul] at hcurv
  have hf : |sourceCurvature (unitCoordinateSpin v) u i j| ≤ (7*m1)^2/2 := by
    exact hcurv.trans (by simpa only [pow_two] using (div_le_div_of_nonneg_right
      (mul_le_mul (hd i) (hd j) (norm_nonneg _) (by positivity : 0 ≤ 7*m1)) (by norm_num : (0 : ℝ) ≤ 2)))
  rw [sourceCurvatureMoment,abs_mul]
  have hw : |u i| ≤ 1 := by rw [abs_of_nonneg (hucube i).1]; exact (hucube i).2
  simpa only [one_mul] using mul_le_mul hw hf (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Original `unitSourceMoment_integral_bound` guarantee for the `SourceMeanBound` construction; the complete source hypotheses are retained. -/
theorem unitSourceMoment_integral_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (m1 : ℝ) (hm1 : 0 ≤ m1)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖sourcePhysicalPartial v i x‖ ≤ m1) (i j : Fin 3) :
    |unitCubeIntegral (sourceCurvatureMoment (unitCoordinateSpin v) i j)| ≤ (7*m1)^2/2 :=
  unitCubeIntegral_abs_le _ _ (fun u hucube => unitSourceMoment_abs_le v hv hu m1 hm1 hb u hucube i j)

/-- Original `unitSourceMoment_integral_zero` guarantee for the `SourceMeanBound` construction; the complete source hypotheses are retained. -/
theorem unitSourceMoment_integral_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖sourcePhysicalPartial v i x‖ ≤ 0) (i j : Fin 3) :
    unitCubeIntegral (sourceCurvatureMoment (unitCoordinateSpin v) i j)=0 := by
  have h := unitSourceMoment_integral_bound v hv hu 0 (by norm_num) hb i j
  norm_num only [mul_zero,zero_pow (by decide : 2≠0),zero_div] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end Qatlib.Concepts.EffectiveGauge.RationalFlow
