/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalRegularity

import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Finite energy of the rational Bateman field

[Kedia2013TyingKnots], equation (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The pointwise decay of the explicit Bateman field gives finite energy at each
time with respect to Lebesgue measure on Euclidean three-space.
-/

public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3)

/-- The squared norm of each field component is integrable over the entire
Euclidean spatial slice at every fixed time. -/
theorem integrable_normSq_rationalField (t : ℝ) (j : Fin 3) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      Complex.normSq (rationalField (s 0) (s 1) (s 2) t j)) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < 8 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hprofile : Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      (1 + ‖s‖ ^ 2) ^ (-(4 : ℝ))) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hdim
    convert h using 2
    norm_num
  have hcoords : Continuous (fun s : EuclideanSpace ℝ (Fin 3) =>
      (s 0, s 1, s 2, t)) :=
    (PiLp.continuous_apply 2 _ 0).prodMk
      ((PiLp.continuous_apply 2 _ 1).prodMk
        ((PiLp.continuous_apply 2 _ 2).prodMk continuous_const))
  have hcont := Complex.continuous_normSq.comp
    ((contDiff_rationalField j).continuous.comp hcoords)
  refine (hprofile.const_mul (14745600 * (1 + t ^ 2) ^ 12)).mono_nonneg
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun _ => Complex.normSq_nonneg _) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  have hnorm : ‖s‖ ^ 2 = s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  rw [hnorm]
  have hpos : 0 ≤ 1 + (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2) := by positivity
  rw [Real.rpow_neg hpos]
  change _ ≤ _ * (((1 + (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2)) ^ ((4 : ℕ) : ℝ))⁻¹)
  rw [Real.rpow_natCast]
  rw [← div_eq_mul_inv]
  simpa only [add_assoc] using normSq_rationalField_le (s 0) (s 1) (s 2) t j

/-- The full energy density of the rational Bateman field is integrable over
Euclidean three-space at every time. -/
theorem rationalField_energy_integrable (t : ℝ) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin 3, Complex.normSq (rationalField (s 0) (s 1) (s 2) t j)) :=
  integrable_finsetSum Finset.univ fun j _ => integrable_normSq_rationalField t j

/-- The sum of the electric and magnetic squared lengths has a finite
spatial integral at every fixed time. -/
theorem rationalField_electric_magnetic_energy_integrable (t : ℝ) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      dot3 (fun j => (rationalField (s 0) (s 1) (s 2) t j).re)
        (fun j => (rationalField (s 0) (s 1) (s 2) t j).re) +
      dot3 (fun j => (rationalField (s 0) (s 1) (s 2) t j).im)
        (fun j => (rationalField (s 0) (s 1) (s 2) t j).im)) := by
  refine (rationalField_energy_integrable t).congr
    (Filter.Eventually.of_forall fun s => ?_)
  exact rationalField_energy_density (s 0) (s 1) (s 2) t

end Qatlib.Papers.KnotLight13.TorusFamily
