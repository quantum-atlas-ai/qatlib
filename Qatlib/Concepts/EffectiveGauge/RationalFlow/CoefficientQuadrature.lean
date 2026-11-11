/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ComplexCube
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ComplexGrid
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ComplexLipschitz
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierIntegrationByParts

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficient Quadrature

Rational Flow constructions for Effective Gauge.
Defines `exactFourierCoefficientGrid`.
Proves `fourierIntegrand_partial_bound`, `unitFourierCoefficient_grid_error`, `complexProduct_sample_mode_error`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of exact Fourier Coefficient Grid in the Rational Flow construction. -/
def exactFourierCoefficientGrid (f : SpatialPoint → ℂ) (k : SpatialFrequency) (M : ℕ) : ℂ :=
  complexGridAverage M (fun a b c =>
    let u := meanTensorSpatial ((a : ℝ)/(M : ℝ),(b : ℝ)/(M : ℝ),(c : ℝ)/(M : ℝ))
    unitFourierMode (-k) u*f u)

/-- Original `fourierIntegrand_partial_bound` guarantee for the `CoefficientQuadrature` construction; the complete source hypotheses are retained. -/
theorem fourierIntegrand_partial_bound (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (k : SpatialFrequency) (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (C0 C1 : ℝ)
    (hb0 : ∀ x, InUnitCube x → ‖f x‖ ≤ C0)
    (hb1 : ∀ x, InUnitCube x → ∀ i, ‖spatialWordPartial f [i] x‖ ≤ C1)
    (x : SpatialPoint) (hx : InUnitCube x) (i : Fin 3) :
    ‖spatialWordPartial (fun y => unitFourierMode (-k) y*f y) [i] x‖ ≤
      C1+7*(N : ℝ)*C0 := by
  have hL : physicalPeriod ≤ (7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have habs : ‖(k i : ℂ)‖=|(k i : ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  have hfactor : ‖(physicalPeriod : ℂ)*Complex.I*((-k) i : ℂ)‖ ≤ 7*(N : ℝ) := by
    simp only [Pi.neg_apply,Int.cast_neg,norm_neg,norm_mul,Complex.norm_I,mul_one,
      Complex.norm_real,Real.norm_of_nonneg physicalPeriod_pos.le,habs]
    exact mul_le_mul hL (hk i) (abs_nonneg _) (by norm_num)
  have hd := congrFun (spatialWordPartial_complex_mul_first (unitFourierMode (-k)) f
    (contDiff_unitFourierMode (-k)) hf i) x
  rw [unitFourierMode_first] at hd
  rw [hd]
  calc
    _ ≤ ‖(physicalPeriod : ℂ)*Complex.I*((-k) i : ℂ)‖*‖f x‖+
        ‖spatialWordPartial f [i] x‖ := by
      simpa only [norm_mul,unitFourierMode_norm,mul_one,one_mul] using norm_add_le
        (((physicalPeriod : ℂ)*Complex.I*((-k) i : ℂ))*unitFourierMode (-k) x*f x)
        (unitFourierMode (-k) x*spatialWordPartial f [i] x)
    _ ≤ (7*(N : ℝ))*C0+C1 := add_le_add
      (mul_le_mul hfactor (hb0 x hx) (norm_nonneg _) (by positivity)) (hb1 x hx i)
    _ = _ := by ring

/-- The exact coefficient's true cube integral is approximated by the
executed mesh, paying 3D/M in the complex norm, including the DC mode. -/
theorem unitFourierCoefficient_grid_error (M : ℕ) (hM : 0<M) (f : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f)
    (k : SpatialFrequency) (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (C0 C1 : ℝ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hb0 : ∀ x, InUnitCube x → ‖f x‖ ≤ C0)
    (hb1 : ∀ x, InUnitCube x → ∀ i, ‖spatialWordPartial f [i] x‖ ≤ C1) :
    ‖unitFourierCoefficient f hf.continuous hp k-exactFourierCoefficientGrid f k M‖ ≤
      3*(C1+7*(N : ℝ)*C0)/(M : ℝ) := by
  let g := fun x => unitFourierMode (-k) x*f x
  have hg : ContDiff ℝ ∞ g := (contDiff_unitFourierMode (-k)).mul hf
  have hD : 0 ≤ C1+7*(N : ℝ)*C0 := by positivity
  have hLip := unitCube_complex_partial_lipschitz g hg (C1+7*(N : ℝ)*C0) hD
    (fun x hx i => fourierIntegrand_partial_bound f hf k N hk C0 C1 hb0 hb1 x hx i)
  have h := unitComplexCubeIntegral_tensor_error M hM g hg.continuous (C1+7*(N : ℝ)*C0) hD hLip
  rw [complexMeanTensorLeftSum_eq_grid] at h
  rw [unitFourierCoefficient_eq_cubeIntegral]
  exact h

/-- Original `complexProduct_sample_mode_error` guarantee for the `CoefficientQuadrature` construction; the complete source hypotheses are retained. -/
theorem complexProduct_sample_mode_error (e ehat c chat : ℂ) (C0 s d : ℝ)
    (he : ‖e‖=1) (hc : ‖c‖ ≤ C0) (hs : ‖chat-c‖ ≤ s) (hd : ‖ehat-e‖ ≤ d) :
    ‖ehat*chat-e*c‖ ≤ s+(C0+s)*d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hchat : ‖chat‖ ≤ C0+s := by
    have h := norm_add_le (chat-c) c
    rw [sub_add_cancel] at h
    linarith
  have heq : ehat*chat-e*c=(ehat-e)*chat+e*(chat-c) := by ring
  calc
    _ ≤ ‖ehat-e‖*‖chat‖+‖chat-c‖ := by
      rw [heq]
      simpa only [norm_mul,he,one_mul] using norm_add_le ((ehat-e)*chat) (e*(chat-c))
    _ ≤ d*(C0+s)+s := add_le_add (mul_le_mul hd hchat (norm_nonneg _) hd0) hs
    _ = _ := by ring

end Qatlib.Concepts.EffectiveGauge.RationalFlow
