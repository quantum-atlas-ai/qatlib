/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisApproximation
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierMode
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Mode Approximation

Torus Fourier constructions for Effective Gauge.
Defines `rationalFourierMode`.
Proves `complexPhase_lipschitz`, `unitFourierMode_eq_complexPhase`, `frequencyLinear_unitCube_bound`.
-/


set_option autoImplicit false
noncomputable section
open Set Finset
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `complexPhase_lipschitz` guarantee for the `FourierModeApproximation` construction; the complete source hypotheses are retained. -/
theorem complexPhase_lipschitz (a b : ℝ) : ‖complexPhase a-complexPhase b‖ ≤ |a-b| := by
  have h := phase_lipschitz a b
  rw [← complexPhase_quaternion a,← complexPhase_quaternion b,← map_sub,norm_ofComplex] at h
  exact h

/-- Original `unitFourierMode_eq_complexPhase` guarantee for the `FourierModeApproximation` construction; the complete source hypotheses are retained. -/
theorem unitFourierMode_eq_complexPhase (k : SpatialFrequency) (x : SpatialPoint) :
    unitFourierMode k x=complexPhase (physicalPeriod*frequencyLinear k x) := by
  rw [complexPhase_eq_exp]
  unfold unitFourierMode fourierModeExponent
  congr 1
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.ofReal_mul]
  ring

/-- Original `frequencyLinear_unitCube_bound` guarantee for the `FourierModeApproximation` construction; the complete source hypotheses are retained. -/
theorem frequencyLinear_unitCube_bound (k : SpatialFrequency) (N : ℕ)
    (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ)) (x : SpatialPoint) (hx : InUnitCube x) :
    |frequencyLinear k x| ≤ 3*(N : ℝ) := by
  rw [frequencyLinear_apply]
  calc
    _ ≤ ∑ i : Fin 3, |(k i : ℝ)*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hxi : |x i| ≤ 1 := by rw [abs_of_nonneg (hx i).1]; exact (hx i).2
      exact (mul_le_mul (hk i) hxi (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

/-- Original `rationalFrequencyLinear_cast` guarantee for the `FourierModeApproximation` construction; the complete source hypotheses are retained. -/
theorem rationalFrequencyLinear_cast (k : SpatialFrequency) (a : Fin 3 → ℚ) :
    ((∑ i : Fin 3, (k i : ℚ)*a i : ℚ) : ℝ)=frequencyLinear k (rationalSpatialPoint a) := by
  rw [frequencyLinear_apply]
  push_cast
  rfl

/-- Definition of rational Fourier Mode in the Torus Fourier construction. -/
def rationalFourierMode (length : ℚ) (k : SpatialFrequency) (a : Fin 3 → ℚ)
    (tolerance : ℚ) : RationalCisResult :=
  rationalCis (length*(∑ i : Fin 3, (k i : ℚ)*a i)) (tolerance/2)

/-- The finite cis output need not be unit. Its true angle error includes
the actual approximate period and the signed frequency. -/
theorem rationalFourierMode_error (length : ℚ) (k : SpatialFrequency) (a : Fin 3 → ℚ)
    (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (ha : ∀ i, (a i : ℝ)∈Set.Icc 0 1) (ell : ℝ) (hl : |(length : ℝ)-physicalPeriod| ≤ ell) :
    ‖rationalCircleCast (rationalFourierMode length k a tolerance).value-
      unitFourierMode k (rationalSpatialPoint a)‖ ≤ (tolerance : ℝ)/2+3*(N : ℝ)*ell := by
  let angle : ℚ := length*(∑ i : Fin 3, (k i : ℚ)*a i)
  have htHalf : 0<tolerance/2 := by positivity
  have hs := rationalCis_spec angle (tolerance/2) htHalf (by linarith)
  have hcis : ‖rationalCircleCast (rationalFourierMode length k a tolerance).value-
      complexPhase (angle : ℝ)‖ ≤ (tolerance : ℝ)/2 := by
    exact hs.1.trans (by exact_mod_cast hs.2.2.1)
  have hangle : |(angle : ℝ)-physicalPeriod*frequencyLinear k (rationalSpatialPoint a)| ≤
      3*(N : ℝ)*ell := by
    have hcast : (angle : ℝ)=(length : ℝ)*frequencyLinear k (rationalSpatialPoint a) := by
      dsimp only [angle]
      rw [Rat.cast_mul,rationalFrequencyLinear_cast]
    rw [hcast,← sub_mul,abs_mul]
    have hdot := frequencyLinear_unitCube_bound k N hk (rationalSpatialPoint a) ha
    have hell : 0 ≤ ell := (abs_nonneg _).trans hl
    exact (mul_le_mul hl hdot (abs_nonneg _) hell).trans_eq (by ring)
  have hphase : ‖complexPhase (angle : ℝ)-unitFourierMode k (rationalSpatialPoint a)‖ ≤
      3*(N : ℝ)*ell := by
    rw [unitFourierMode_eq_complexPhase]
    exact (complexPhase_lipschitz _ _).trans hangle
  have htri := dist_triangle (rationalCircleCast (rationalFourierMode length k a tolerance).value)
    (complexPhase (angle : ℝ)) (unitFourierMode k (rationalSpatialPoint a))
  simp only [dist_eq_norm] at htri
  exact htri.trans (add_le_add hcis hphase)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
