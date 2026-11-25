/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaInitialPotential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Full-space magnetic helicity at the initial time

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
The pointwise initial helicity density from the verified vector potential
is integrable over all of Euclidean three-space. Radial integration and
the primitive of the rational radial integrand give magnetic helicity
`1/4` with the stated field normalization and spatial orientation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Filter MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open scoped Topology

/-- A primitive for the radial integrand in the magnetic helicity integral. -/
private noncomputable def helicityPrimitive (r : ℝ) : ℝ :=
  (Real.arctan r - r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) / 8

/-- The primitive has the stated rational derivative, including at zero. -/
private theorem hasDerivAt_helicity_primitive (r : ℝ) :
    HasDerivAt helicityPrimitive (r ^ 2 / (1 + r ^ 2) ^ 3) r := by
  have hval : 0 < 1 + r ^ 2 := by positivity
  have hS := ((hasDerivAt_id r).pow 2).const_add 1
  have hN := (hasDerivAt_id r).mul (((hasDerivAt_id r).pow 2).const_sub 1)
  have h := (Real.hasDerivAt_arctan r).sub (hN.div (hS.pow 2) (pow_ne_zero 2 hval.ne'))
  unfold helicityPrimitive
  convert h.div_const (8 : ℝ) using 1
  · funext u
    simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      one_mul, mul_one]
    field_simp [hval.ne']
    ring

/-- The rational term in the primitive vanishes at positive infinity.
Rewriting it using the inverse radius gives a continuous function at zero. -/
private theorem tendsto_helicity_primitive_tail :
    Tendsto (fun r : ℝ => r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) atTop (𝓝 0) := by
  let g : ℝ → ℝ := fun u => u * (u ^ 2 - 1) / (1 + u ^ 2) ^ 2
  have hg : ContinuousAt g 0 := by
    change ContinuousAt (fun u : ℝ => (u * (u ^ 2 - 1)) / (1 + u ^ 2) ^ 2) 0
    exact ((continuous_id.mul ((continuous_id.pow 2).sub continuous_const)).continuousAt).div
      (((continuous_const.add (continuous_id.pow 2)).pow 2).continuousAt)
      (by norm_num)
  have hlim : Tendsto (fun r : ℝ => g r⁻¹) atTop (𝓝 0) := by
    simpa [g, Function.comp_def] using hg.tendsto.comp tendsto_inv_atTop_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hS : 0 < 1 + r ^ 2 := by positivity
  have hSi : 0 < 1 + (r⁻¹) ^ 2 := by positivity
  dsimp [g]
  field_simp [hr.ne', hS.ne', hSi.ne']
  ring

/-- The primitive approaches pi divided by sixteen at positive infinity. -/
private theorem tendsto_helicity_primitive :
    Tendsto helicityPrimitive atTop (𝓝 (Real.pi / 16)) := by
  have h : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have h' := (h.sub tendsto_helicity_primitive_tail).div_const (8 : ℝ)
  have hval : (Real.pi / 2 - 0) / 8 = Real.pi / 16 := by ring
  change Tendsto (fun r : ℝ => (Real.arctan r - r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) / 8)
    atTop (𝓝 (Real.pi / 16))
  simpa only [hval] using h'

/-- The derivative is nonnegative and has a finite integral on the positive
half-axis. -/
private theorem integrable_helicity_radial :
    IntegrableOn (fun r : ℝ => r ^ 2 / (1 + r ^ 2) ^ 3) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_helicity_primitive r)
    (fun r _ => by positivity) tendsto_helicity_primitive

/-- The exact radial integral after including the spherical Jacobian. -/
private theorem integral_helicity_radial :
    (∫ r in Ioi (0 : ℝ), r ^ 2 / (1 + r ^ 2) ^ 3) = Real.pi / 16 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun r _ => hasDerivAt_helicity_primitive r)
    (fun r _ => by positivity) tendsto_helicity_primitive]
  simp [helicityPrimitive]

/-- The stereographic radial profile is integrable on Euclidean three-space. -/
private theorem integrable_hopf_profile :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) => 1 / (1 + ‖s‖ ^ 2) ^ 3) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (f := fun r : ℝ => 1 / (1 + r ^ 2) ^ 3)).2
  simpa only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul, mul_one_div] using
    integrable_helicity_radial

/-- The stereographic profile integrates to pi squared divided by four. -/
private theorem integral_hopf_profile :
    (∫ s : EuclideanSpace ℝ (Fin 3), 1 / (1 + ‖s‖ ^ 2) ^ 3) = Real.pi ^ 2 / 4 := by
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun r : ℝ => 1 / (1 + r ^ 2) ^ 3)]
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul, mul_one_div, nsmul_eq_mul,
    Nat.cast_ofNat, integral_helicity_radial, measureReal_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

/-- The dot product of the explicit initial vector potential with the
actual magnetic field, as an integrand on Euclidean three-space. -/
noncomputable def ranadaInitialHelicityDensity (s : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  dot3 (ranadaInitialPotential (s 0) (s 1) (s 2))
    (fun j => (ranadaB (s 0) (s 1) (s 2) 0 j).re)

/-- The magnetic helicity density is the stereographic radial profile
times the inverse square of pi. -/
theorem ranada_initial_helicity_density_eq_radial (s : EuclideanSpace ℝ (Fin 3)) :
    ranadaInitialHelicityDensity s = (1 / Real.pi ^ 2) * (1 / (1 + ‖s‖ ^ 2) ^ 3) := by
  have hs : hopfScale (s 0) (s 1) (s 2) = 1 + ‖s‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    unfold hopfScale
    ring
  rw [ranadaInitialHelicityDensity, ranada_initial_helicity_density, hs]
  field_simp [Real.pi_ne_zero]

/-- The initial helicity density is absolutely integrable on the full
spatial slice. -/
theorem integrable_ranada_initial_helicity : Integrable ranadaInitialHelicityDensity :=
  (integrable_hopf_profile.const_mul (1 / Real.pi ^ 2)).congr
    (Filter.Eventually.of_forall fun s => (ranada_initial_helicity_density_eq_radial s).symm)

/-- The total magnetic helicity at time zero is one quarter for the
explicit smooth gauge and field normalization used here. -/
theorem integral_ranada_initial_helicity :
    (∫ s : EuclideanSpace ℝ (Fin 3), ranadaInitialHelicityDensity s) = 1 / 4 := by
  simp_rw [ranada_initial_helicity_density_eq_radial]
  rw [integral_const_mul, integral_hopf_profile]
  field_simp [Real.pi_ne_zero]

end Qatlib.Papers.KnottedLight08.HopfField
