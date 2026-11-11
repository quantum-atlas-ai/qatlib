/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.PhysicalH1Energy
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeCoordinates

set_option backward.isDefEq.respectTransparency false

/-!
# Quaternion H1 Energy

Spectral H1 constructions for Effective Gauge.
Proves `quaternion_norm_sq_eq_coordinate_sum`, `unitBoxEnergy_coordinates`, `unitFieldH1Energy_coordinates`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `quaternion_norm_sq_eq_coordinate_sum` guarantee for the `QuaternionH1Energy` construction; the complete source hypotheses are retained. -/
theorem quaternion_norm_sq_eq_coordinate_sum (q : ℍ) :
    ‖q‖^2=∑ j : Fin 4, ‖quaternionCoordinateCLM j q‖^2 := by
  have h := Quaternion.normSq_eq_norm_mul_self q
  rw [Quaternion.normSq_def'] at h
  simp only [Fin.sum_univ_succ]
  change ‖q‖^2=‖q.re‖^2+(‖q.imI‖^2+(‖q.imJ‖^2+(‖q.imK‖^2+0)))
  simp only [Real.norm_eq_abs,sq_abs]
  nlinarith

/-- Original `unitBoxEnergy_coordinates` guarantee for the `QuaternionH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitBoxEnergy_coordinates (Q : QuaternionField) (hQ : Continuous Q) :
    unitBoxEnergy Q=∑ j : Fin 4, unitBoxEnergy (fun x => quaternionCoordinateCLM j (Q x)) := by
  simp_rw [unitBoxEnergy_eq_unitCubeIntegral]
  unfold unitCubeIntegral
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hi (j : Fin 4) : IntegrableOn (fun u : Fin 3 → ℝ => ‖quaternionCoordinateCLM j (Q (WithLp.toLp 2 u))‖^2)
      (Icc (0 : Fin 3 → ℝ) (fun _ => (1 : ℝ))) :=
    ((((quaternionCoordinateCLM j).continuous.comp hQ).comp e.continuous).norm.pow 2).integrableOn_Icc
  rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => quaternion_norm_sq_eq_coordinate_sum (Q (WithLp.toLp 2 u)))

/-- Original `unitFieldH1Energy_coordinates` guarantee for the `QuaternionH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitFieldH1Energy_coordinates (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q) :
    unitFieldH1Energy Q=∑ j : Fin 4, unitFieldH1Energy (fun x => quaternionCoordinateCLM j (Q x)) := by
  unfold unitFieldH1Energy
  rw [unitBoxEnergy_coordinates Q hQ.continuous]
  have hgrad (i : Fin 3) : unitBoxEnergy (spatialWordPartial Q [i])=
      ∑ j : Fin 4, unitBoxEnergy (spatialWordPartial (fun x => quaternionCoordinateCLM j (Q x)) [i]) := by
    rw [unitBoxEnergy_coordinates (spatialWordPartial Q [i])
      (contDiff_spatialWordPartial Q hQ [i]).continuous]
    apply Finset.sum_congr rfl
    intro j _
    rw [spatialWordPartial_clm (quaternionCoordinateCLM j) Q hQ]
  simp_rw [hgrad]
  rw [Finset.sum_comm,Finset.sum_div,Finset.sum_add_distrib]

/-- Original `unitBoxEnergy_re_le` guarantee for the `QuaternionH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitBoxEnergy_re_le (f : SpatialPoint → ℂ) (hf : Continuous f) :
    unitBoxEnergy (fun x => (f x).re) ≤ unitBoxEnergy f := by
  rw [unitBoxEnergy_eq_unitCubeIntegral,unitBoxEnergy_eq_unitCubeIntegral]
  unfold unitCubeIntegral
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hi : IntegrableOn (fun u : Fin 3 → ℝ => ‖f (WithLp.toLp 2 u)‖^2)
      (Icc (0 : Fin 3 → ℝ) (fun _ => (1 : ℝ))) :=
    ((hf.comp e.continuous).norm.pow 2).integrableOn_Icc
  have hr : IntegrableOn (fun u : Fin 3 → ℝ => ‖(f (WithLp.toLp 2 u)).re‖^2)
      (Icc (0 : Fin 3 → ℝ) (fun _ => (1 : ℝ))) :=
    (((Complex.continuous_re.comp hf).comp e.continuous).norm.pow 2).integrableOn_Icc
  apply integral_mono hr hi
  intro u
  apply (sq_le_sq₀ (norm_nonneg ((f (WithLp.toLp 2 u)).re)) (norm_nonneg (f (WithLp.toLp 2 u)))).mpr
  simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (f (WithLp.toLp 2 u))

/-- Original `unitFieldH1Energy_re_le` guarantee for the `QuaternionH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitFieldH1Energy_re_le (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f) :
    unitFieldH1Energy (fun x => (f x).re) ≤ unitFieldH1Energy f := by
  unfold unitFieldH1Energy
  apply add_le_add (unitBoxEnergy_re_le f hf.continuous)
  apply div_le_div_of_nonneg_right _ (sq_nonneg physicalPeriod)
  apply Finset.sum_le_sum
  intro i _
  change unitBoxEnergy (spatialWordPartial (fun x => Complex.reCLM (f x)) [i]) ≤ _
  rw [spatialWordPartial_clm Complex.reCLM f hf]
  exact unitBoxEnergy_re_le (spatialWordPartial f [i]) (contDiff_spatialWordPartial f hf [i]).continuous

end Qatlib.Concepts.EffectiveGauge.SpectralH1
