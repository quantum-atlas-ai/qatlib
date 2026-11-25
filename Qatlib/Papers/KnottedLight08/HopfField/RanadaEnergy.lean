/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaBateman
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalEnergy

import Qatlib.Papers.KnottedLight08.HopfField.RanadaMaxwell
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

/-!
# Spatial decay and finite energy of the Rañada field

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
The exact relation to the rational Bateman field supplies spatial decay
and integrability of every squared field component at each fixed time.
The resulting integrable energy density is the sum of the actual
electric and magnetic squared lengths in Euclidean three-space.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Bornology Filter MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Qatlib.Papers.KnotLight13.TorusFamily
open scoped ComplexConjugate Topology

/-- The reflected Bateman energy density at a single component scales
by the squared modulus of the exact Rañada prefactor. -/
theorem normSq_ranada_field (x y z t : ℝ) (j : Fin 3) :
    Complex.normSq (ranadaField x y z t j) =
      Complex.normSq (Complex.I / (2 * (Real.pi : ℂ))) *
        Complex.normSq (rationalField x y z (-t) j) := by
  rw [ranadaField_eq_bateman, Complex.normSq_mul, Complex.normSq_conj]

/-- Each squared field component decays at least as the fourth inverse
power of the radial denominator at any fixed time. -/
theorem normSq_ranada_field_le (x y z t : ℝ) (j : Fin 3) :
    Complex.normSq (ranadaField x y z t j) ≤
      Complex.normSq (Complex.I / (2 * (Real.pi : ℂ))) *
        (14745600 * (1 + t ^ 2) ^ 12 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4) := by
  rw [normSq_ranada_field]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [even_two.neg_pow] using normSq_rationalField_le x y z (-t) j)
    (Complex.normSq_nonneg _)

/-- The square-root of the pointwise squared field bound has the radial
denominator to the second power. -/
private theorem norm_le_sqrt_div_sq {w : ℂ} {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (h : Complex.normSq w ≤ C / R ^ 4) : ‖w‖ ≤ Real.sqrt C / R ^ 2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hR.le 2))).mp
  rw [Complex.sq_norm, div_pow, Real.sq_sqrt hC, ← pow_mul]
  exact h

/-- In three real dimensions, the squared radial bound implies absolute integrability. -/
private theorem integrable_of_normSq_le_radial {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ s, Complex.normSq (f s) ≤ C / (1 + ‖s‖ ^ 2) ^ 4) : Integrable f := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < 4 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hg : Integrable (fun s : EuclideanSpace ℝ (Fin 3) => (1 + ‖s‖ ^ 2) ^ (-(2 : ℝ))) := by
    simpa only [show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num] using
      integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hdim
  refine (hg.const_mul (Real.sqrt C)).mono' hf.aestronglyMeasurable ?_
  filter_upwards with s
  have hR : 0 < 1 + ‖s‖ ^ 2 := by positivity
  change ‖f s‖ ≤ Real.sqrt C * (1 + ‖s‖ ^ 2) ^ (-(2 : ℝ))
  rw [Real.rpow_neg hR.le]
  change _ ≤ Real.sqrt C * (((1 + ‖s‖ ^ 2) ^ ((2 : ℕ) : ℝ))⁻¹)
  rw [Real.rpow_natCast, ← div_eq_mul_inv]
  exact norm_le_sqrt_div_sq hC hR (hBound s)

/-- Each actual field component is absolutely integrable on the Euclidean spatial slice. -/
theorem integrable_ranada_field (t : ℝ) (j : Fin 3) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) => ranadaField (s 0) (s 1) (s 2) t j) := by
  let C := Complex.normSq (Complex.I / (2 * (Real.pi : ℂ))) *
    (14745600 * (1 + t ^ 2) ^ 12)
  have hCt : 0 ≤ 14745600 * (1 + t ^ 2) ^ 12 :=
    mul_nonneg (by norm_num) (pow_nonneg (add_nonneg zero_le_one (sq_nonneg t)) 12)
  have hC : 0 ≤ C := mul_nonneg (Complex.normSq_nonneg _) hCt
  have hp : Continuous (fun s : EuclideanSpace ℝ (Fin 3) => (s 0, s 1, s 2, t)) :=
    (PiLp.continuous_apply 2 _ 0).prodMk
      ((PiLp.continuous_apply 2 _ 1).prodMk ((PiLp.continuous_apply 2 _ 2).prodMk continuous_const))
  have hf : Continuous (fun s : EuclideanSpace ℝ (Fin 3) => ranadaField (s 0) (s 1) (s 2) t j) := by
    simpa only [Function.comp_def, ranadaFieldAt] using
      (contDiff_ranadaField j).continuous.comp hp
  refine integrable_of_normSq_le_radial (C := C) hf hC fun s => ?_
  have hnorm : 1 + ‖s‖ ^ 2 = 1 + (s 0) ^ 2 + (s 1) ^ 2 + (s 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    ring
  dsimp only [C]
  rw [hnorm, mul_div_assoc]
  exact normSq_ranada_field_le (s 0) (s 1) (s 2) t j

/-- The complex field components tend to zero at spatial infinity
on each fixed-time slice. -/
theorem tendsto_ranada_field_spatial_infinity (t : ℝ) (j : Fin 3) :
    Tendsto (fun s : EuclideanSpace ℝ (Fin 3) => ranadaField (s 0) (s 1) (s 2) t j)
      (cobounded (EuclideanSpace ℝ (Fin 3))) (𝓝 0) := by
  let κ := Complex.normSq (Complex.I / (2 * (Real.pi : ℂ)))
  let C := κ * (14745600 * (1 + t ^ 2) ^ 12)
  have hnorm := tendsto_norm_cobounded_atTop (E := EuclideanSpace ℝ (Fin 3))
  have hSq : Tendsto (fun s : EuclideanSpace ℝ (Fin 3) => ‖s‖ ^ 2) (cobounded _) atTop :=
    (tendsto_pow_atTop (n := 2) (by decide)).comp hnorm
  have hden : Tendsto (fun s : EuclideanSpace ℝ (Fin 3) => (1 + ‖s‖ ^ 2) ^ 4)
      (cobounded _) atTop :=
    (tendsto_pow_atTop (n := 4) (by decide)).comp (tendsto_atTop_add_const_left _ 1 hSq)
  have hmajor : Tendsto (fun s : EuclideanSpace ℝ (Fin 3) => C / (1 + ‖s‖ ^ 2) ^ 4)
      (cobounded _) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  have hle (s : EuclideanSpace ℝ (Fin 3)) :
      Complex.normSq (ranadaField (s 0) (s 1) (s 2) t j) ≤ C / (1 + ‖s‖ ^ 2) ^ 4 := by
    have hs : 1 + ‖s‖ ^ 2 = 1 + (s 0) ^ 2 + (s 1) ^ 2 + (s 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      ring
    rw [hs]
    simpa only [C, κ, mul_div_assoc] using normSq_ranada_field_le (s 0) (s 1) (s 2) t j
  have hSquared : Tendsto
      (fun s : EuclideanSpace ℝ (Fin 3) => Complex.normSq (ranadaField (s 0) (s 1) (s 2) t j))
      (cobounded _) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ => Complex.normSq_nonneg _) hle
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [Complex.norm_def, Real.sqrt_zero] using hSquared.sqrt

/-- A squared field component is integrable on the entire spatial slice. -/
theorem integrable_normSq_ranada_field (t : ℝ) (j : Fin 3) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      Complex.normSq (ranadaField (s 0) (s 1) (s 2) t j)) := by
  refine ((integrable_normSq_rationalField (-t) j).const_mul
    (Complex.normSq (Complex.I / (2 * (Real.pi : ℂ))))).congr ?_
  exact Filter.Eventually.of_forall fun s =>
    (normSq_ranada_field (s 0) (s 1) (s 2) t j).symm

/-- The field squared norm is the sum of the electric and magnetic squared
lengths under the actual Rañada decomposition. -/
theorem ranada_energy_density (x y z t : ℝ) :
    ∑ j : Fin 3, Complex.normSq (ranadaField x y z t j) =
      dot3 (fun j => (ranadaE x y z t j).re) (fun j => (ranadaE x y z t j).re) +
      dot3 (fun j => (ranadaB x y z t j).re) (fun j => (ranadaB x y z t j).re) := by
  simp only [Fin.sum_univ_three, Complex.normSq_apply, dot3, ranadaField, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, ranadaE_im, ranadaB_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, one_mul, zero_add, add_zero]
  ring

/-- The total electric and magnetic energy density is integrable
at every time, with respect to Lebesgue measure on the full spatial slice. -/
theorem integrable_ranada_energy (t : ℝ) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      dot3 (fun j => (ranadaE (s 0) (s 1) (s 2) t j).re) (fun j => (ranadaE (s 0) (s 1) (s 2) t j).re) +
      dot3 (fun j => (ranadaB (s 0) (s 1) (s 2) t j).re) (fun j => (ranadaB (s 0) (s 1) (s 2) t j).re)) := by
  refine (integrable_finsetSum Finset.univ fun j _ => integrable_normSq_ranada_field t j).congr ?_
  exact Filter.Eventually.of_forall fun s => ranada_energy_density (s 0) (s 1) (s 2) t

end Qatlib.Papers.KnottedLight08.HopfField
