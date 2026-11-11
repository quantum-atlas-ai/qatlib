/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.GroverInterp.UnitarySpectrumAux
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Linarith

/-!
# Geometric estimates for Grover amplitudes

This module bounds the effect of normalization and approximate norm-preserving evolution on
target amplitudes. It also proves that a unitary matrix preserves the Euclidean norm, providing
the geometric estimates used in Grover interpolation.

For background, see [Grover1996].

## Main statements

* `grover_normalize_near_unit`: normalization doubles the relative approximation bound at most.
* `grover_amplitude_of_near_rotation`: transfer of a target overlap through approximate
  evolution.
* `grover_unitary_euclidean_norm`: Euclidean norm preservation by a unitary matrix.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.GroverInterp

/-- If a nonzero vector is within `η * C` of a positive multiple `C` of a unit vector, its
normalization is within `2 * η` of that unit vector. -/
theorem grover_normalize_near_unit {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (s v : V) (C η : ℝ) (hs : ‖s‖ = 1)
    (hC : 0 < C) (hv : v ≠ 0) (hclose : ‖v - C • s‖ ≤ η * C) :
    ‖s - NormedSpace.normalize v‖ ≤ 2 * η := by
  let a : V := C⁻¹ • v
  have ha : a ≠ 0 := by
    dsimp [a]
    exact smul_ne_zero (inv_ne_zero hC.ne') hv
  have hdist : ‖a - s‖ ≤ η := by
    have hid : a - s = C⁻¹ • (v - C • s) := by
      dsimp [a]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hC.ne', one_smul]
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹ * ‖v - C • s‖ ≤ C⁻¹ * (η * C) := mul_le_mul_of_nonneg_left hclose (inv_nonneg.mpr hC.le)
      _ = η := by field_simp
  have han : ‖a - NormedSpace.normalize a‖ = |‖a‖ - 1| := by
    calc
      _ = ‖(‖a‖ - 1) • NormedSpace.normalize a‖ := by
        congr 1
        rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
      _ = _ := by rw [norm_smul, NormedSpace.norm_normalize ha, mul_one, Real.norm_eq_abs]
  have hn : |‖a‖ - 1| ≤ ‖a - s‖ := by
    rw [← hs]
    exact abs_norm_sub_norm_le a s
  have hna : NormedSpace.normalize a = NormedSpace.normalize v :=
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hC) v
  calc
    ‖s - NormedSpace.normalize v‖ = ‖s - NormedSpace.normalize a‖ := by rw [hna]
    _ ≤ ‖s - a‖ + ‖a - NormedSpace.normalize a‖ := norm_sub_le_norm_sub_add_norm_sub s a _
    _ ≤ 2 * η := by rw [norm_sub_rev s a, han]; linarith

/-- For a norm-preserving complex linear map, approximating the input within `η` and its image
within `β` lowers the target overlap norm by at most `η + β` when the target norm is at most
one. -/
theorem grover_amplitude_of_near_rotation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →ₗ[ℂ] E) (hnorm : ∀ x, ‖L x‖ = ‖x‖)
    (s v u g : E) (η β : ℝ) (hg : ‖g‖ ≤ 1)
    (hs : ‖s - v‖ ≤ η) (hr : ‖L v - u‖ ≤ β) :
    ‖inner ℂ g u‖ - η - β ≤ ‖inner ℂ g (L s)‖ := by
  have hclose : ‖L s - u‖ ≤ η + β := by
    calc
      _ ≤ ‖L s - L v‖ + ‖L v - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖s - v‖ + ‖L v - u‖ := by rw [← map_sub, hnorm]
      _ ≤ _ := add_le_add hs hr
  have hi : ‖inner ℂ g u - inner ℂ g (L s)‖ ≤ η + β := by
    rw [← inner_sub_right]
    calc
      _ ≤ ‖g‖ * ‖u - L s‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖u - L s‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul, norm_sub_rev u (L s)] using hclose
  have h := norm_sub_norm_le (inner ℂ g u) (inner ℂ g (L s))
  linarith

/-- A complex matrix satisfying `star U * U = 1` preserves the Euclidean norm under its
associated linear map. -/
theorem grover_unitary_euclidean_norm (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hu : star U * U = 1)
    (x : EuclideanSpace ℂ (Fin m)) : ‖U.toEuclideanLin x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [PiLp.norm_sq_eq_of_L2] using! jw_unitary_mulVec_norm_sq m U hu x

end Qatlib.Concepts.WalkFind.GroverInterp
