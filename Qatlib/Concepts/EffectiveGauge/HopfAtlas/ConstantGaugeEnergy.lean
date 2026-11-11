/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.PhysicalH1Energy
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

set_option backward.isDefEq.respectTransparency false

/-!
# Constant Gauge Energy

Hopf Atlas constructions for Effective Gauge.
Proves `cubeIntegrableContinuous`, `physicalCubeIntegral_mono_continuous`, `physicalCubeIntegral_add_continuous`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `cubeIntegrableContinuous` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
private theorem cubeIntegrableContinuous (f : SpatialPoint → ℝ) (hf : Continuous f) :
    IntegrableOn (fun u : Fin 3 → ℝ => f (WithLp.toLp 2 u))
      (Icc (0 : Fin 3 → ℝ) (fun _ => physicalPeriod)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  exact (hf.comp e.continuous).integrableOn_Icc

/-- Original `physicalCubeIntegral_mono_continuous` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_mono_continuous (f g : SpatialPoint → ℝ)
    (hf : Continuous f) (hg : Continuous g) (h : ∀ X, f X ≤ g X) :
    physicalCubeIntegral f ≤ physicalCubeIntegral g :=
  integral_mono (cubeIntegrableContinuous f hf) (cubeIntegrableContinuous g hg) (fun u => h (WithLp.toLp 2 u))

/-- Original `physicalCubeIntegral_add_continuous` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_add_continuous (f g : SpatialPoint → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    physicalCubeIntegral (fun X => f X+g X)=physicalCubeIntegral f+physicalCubeIntegral g :=
  integral_add (cubeIntegrableContinuous f hf) (cubeIntegrableContinuous g hg)

/-- Original `physicalCubeIntegral_const_mul` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_const_mul (f : SpatialPoint → ℝ) (c : ℝ) :
    physicalCubeIntegral (fun X => c*f X)=c*physicalCubeIntegral f := by
  unfold physicalCubeIntegral
  exact integral_const_mul c _

/-- Original `physicalCubeSquare_add_le` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalCubeSquare_add_le (f g : QuaternionField) (hf : Continuous f) (hg : Continuous g) :
    physicalCubeIntegral (fun X => ‖f X+g X‖^2) ≤
      2*physicalCubeIntegral (fun X => ‖f X‖^2)+2*physicalCubeIntegral (fun X => ‖g X‖^2) := by
  have h := physicalCubeIntegral_mono_continuous
    (fun X => ‖f X+g X‖^2) (fun X => 2*‖f X‖^2+2*‖g X‖^2)
    ((hf.add hg).norm.pow 2) (((hf.norm.pow 2).const_mul 2).add ((hg.norm.pow 2).const_mul 2))
    (by intro X; nlinarith [norm_add_le (f X) (g X),norm_nonneg (f X+g X),sq_nonneg (‖f X‖-‖g X‖)])
  rw [physicalCubeIntegral_add_continuous (fun X => 2*‖f X‖^2) (fun X => 2*‖g X‖^2) ((hf.norm.pow 2).const_mul 2)
    ((hg.norm.pow 2).const_mul 2),physicalCubeIntegral_const_mul,physicalCubeIntegral_const_mul] at h
  exact h

/-- Original `spatialWordPartial_constant_left` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_constant_left (c : ℍ) (f : QuaternionField)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) :
    spatialWordPartial (fun X => c*f X) w=fun X => c*spatialWordPartial f w X := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    spatialWordPartial_clm (ContinuousLinearMap.mul ℝ ℍ c) f hf w

/-- Exact equality for the ordinary unnormalized physical H1 energy. -/
theorem physicalFieldH1Energy_constant_left (c : ℍ) (f : QuaternionField) (hf : ContDiff ℝ ∞ f) :
    physicalFieldH1Energy (fun X => c*f X)=‖c‖^2*physicalFieldH1Energy f := by
  unfold physicalFieldH1Energy
  simp_rw [spatialWordPartial_constant_left c f hf,norm_mul,mul_pow,physicalCubeIntegral_const_mul]
  rw [← Finset.mul_sum]
  ring

/-- Original `physicalFieldH1Energy_add_le` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalFieldH1Energy_add_le (f g : QuaternionField)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    physicalFieldH1Energy (fun X => f X+g X) ≤ 2*physicalFieldH1Energy f+2*physicalFieldH1Energy g := by
  have h0 := physicalCubeSquare_add_le f g hf.continuous hg.continuous
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => physicalCubeSquare_add_le (spatialWordPartial f [i]) (spatialWordPartial g [i])
      (contDiff_spatialWordPartial f hf [i]).continuous (contDiff_spatialWordPartial g hg [i]).continuous)
  unfold physicalFieldH1Energy
  simp_rw [spatialWordPartial_add f g hf hg]
  have h := add_le_add h0 hsum
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,mul_add,add_assoc,add_left_comm,add_comm] using h

/-- Original `physicalFieldH1Energy_nonneg` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalFieldH1Energy_nonneg (f : QuaternionField) : 0 ≤ physicalFieldH1Energy f := by
  unfold physicalFieldH1Energy physicalCubeIntegral
  exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

/-- Approximate constant transfer is charged against both the original
approximation error and the target field energy. It is not an isometry. -/
theorem physicalFieldH1Energy_transfer_error (A C : ℍ) (F Q : QuaternionField)
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) :
    physicalFieldH1Energy (fun X => A*F X-C*Q X) ≤
      2*‖A‖^2*physicalFieldH1Energy (fun X => F X-Q X)+
      2*‖A-C‖^2*physicalFieldH1Energy Q := by
  have hid : (fun X => A*F X-C*Q X)=
      (fun X => A*(F X-Q X)+(A-C)*Q X) := by
    funext X
    noncomm_ring
  rw [hid]
  have h := physicalFieldH1Energy_add_le
    (fun X => A*(F X-Q X)) (fun X => (A-C)*Q X)
    (contDiff_const.mul (hF.sub hQ)) (contDiff_const.mul hQ)
  rw [physicalFieldH1Energy_constant_left A _ (hF.sub hQ),
    physicalFieldH1Energy_constant_left (A-C) Q hQ] at h
  simpa only [mul_assoc] using h

/-- Original `physicalFieldH1Energy_unit_bound` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalFieldH1Energy_unit_bound (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q)
    (hu : ∀ X, ‖Q X‖=1) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ (i : Fin 3) X, ‖spatialWordPartial Q [i] X‖ ≤ M) :
    physicalFieldH1Energy Q ≤ physicalPeriod^3*(1+3*M^2) := by
  have h0 : physicalCubeIntegral (fun X => ‖Q X‖^2)=physicalPeriod^3 := by
    simp only [hu,one_pow,physicalCubeIntegral_one]
  have hgrad (i : Fin 3) : physicalCubeIntegral (fun X => ‖spatialWordPartial Q [i] X‖^2) ≤
      physicalPeriod^3*M^2 := by
    have h := physicalCubeIntegral_mono_continuous
      (fun X => ‖spatialWordPartial Q [i] X‖^2) (fun _ => M^2)
      ((contDiff_spatialWordPartial Q hQ [i]).continuous.norm.pow 2) continuous_const
      (fun X => (sq_le_sq₀ (norm_nonneg _) hM).mpr (hder i X))
    have hc : physicalCubeIntegral (fun _ => M^2)=physicalPeriod^3*M^2 := by
      have he : (fun _ : SpatialPoint => M^2)=(fun _ => M^2*1) := by simp only [mul_one]
      rw [he,physicalCubeIntegral_const_mul,physicalCubeIntegral_one,mul_comm]
    exact h.trans_eq hc
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ => hgrad i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  unfold physicalFieldH1Energy
  rw [h0]
  calc
    _ ≤ physicalPeriod^3+(3 : ℕ)*(physicalPeriod^3*M^2) := add_le_add le_rfl hsum
    _ = _ := by push_cast; ring

/-- Original `physicalFieldH1Energy_sub_comm` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalFieldH1Energy_sub_comm (F Q : QuaternionField)
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) :
    physicalFieldH1Energy (fun X => F X-Q X)=physicalFieldH1Energy (fun X => Q X-F X) := by
  have hid : (fun X => F X-Q X)=(fun X => (-1 : ℍ)*(Q X-F X)) := by
    funext X
    noncomm_ring
  rw [hid,physicalFieldH1Energy_constant_left (-1) _ (hQ.sub hF)]
  simp only [norm_neg,norm_one,one_pow,one_mul]

/-- Original `physicalFirstWord_of_normalized_bound` guarantee for the `ConstantGaugeEnergy` construction; the complete source hypotheses are retained. -/
theorem physicalFirstWord_of_normalized_bound (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q)
    (M : ℝ) (hM : ∀ (i : Fin 3) u, ‖spatialWordPartial (fun x => Q (physicalPeriod • x)) [i] u‖ ≤ M)
    (i : Fin 3) (X : SpatialPoint) : ‖spatialWordPartial Q [i] X‖ ≤ M := by
  have hL : (1 : ℝ) ≤ physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  have h := hM i (physicalPeriod⁻¹ • X)
  rw [spatialWordPartial_scale Q hQ physicalPeriod [i]] at h
  simp only [List.length_singleton,pow_one,smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul,
    norm_smul,Real.norm_eq_abs,abs_of_pos physicalPeriod_pos] at h
  have hle := mul_le_mul_of_nonneg_right hL (norm_nonneg (spatialWordPartial Q [i] X))
  exact le_trans (by simpa only [one_mul] using hle) h

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
