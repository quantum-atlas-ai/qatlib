/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.LocalResolventApproximation
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! Scalar-anchor homotopy for the genuine numerical-range resolvent.
The numerical range remains inside the original convex range. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Construction for scalar Anchor Homotopy in the resolvent homotopy model. -/
def scalarAnchorHomotopy (A : Matrix I I ℂ) (c : ℂ) (s : ℝ) : Matrix I I ℂ :=
  c • 1 + (s : ℂ) • (A-c • 1)

/-- The identity or estimate `scalarAnchorHomotopy_rayleigh` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_rayleigh (A : Matrix I I ℂ) (c : ℂ) (s : ℝ)
    (x : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) :
    inner ℂ x ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (scalarAnchorHomotopy A c s)) x) =
      (1-s) • c+s • inner ℂ x ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A) x) := by
    simp only [scalarAnchorHomotopy, map_add, map_sub, map_smul, map_one,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      inner_add_right, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx, one_pow, Complex.ofReal_one, mul_one,
      Complex.real_smul, Complex.ofReal_sub]
    ring

/-- The identity or estimate `scalarAnchorHomotopy_range_subset` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_range_subset (A : Matrix I I ℂ) (c : ℂ)
    (hc : c ∈ matrixNumericalRange A) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    matrixNumericalRange (scalarAnchorHomotopy A c s) ⊆ matrixNumericalRange A := by
  rintro w ⟨x, hx, rfl⟩
  have hAx : inner ℂ x ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A) x) ∈ matrixNumericalRange A :=
    ⟨x, hx, rfl⟩
  have hconv := (numericalRange_convex (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A)) hc hAx
    (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
  have he := scalarAnchorHomotopy_rayleigh A c s x hx
  rwa [he]

/-- The identity or estimate `scalarAnchorHomotopy_separation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_separation (A : Matrix I I ℂ) (c z : ℂ)
    (hc : c ∈ matrixNumericalRange A) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) :
    ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A c s), r ≤ ‖z-w‖ :=
  fun w hw => hsep w (scalarAnchorHomotopy_range_subset A c hc s hs hw)

/-- The identity or estimate `matrixResolvent_eq_ringInverse_of_separation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem matrixResolvent_eq_ringInverse_of_separation (A : Matrix I I ℂ) (z : ℂ)
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) :
    matrixResolvent A z = Ring.inverse (matrixShift A z) := by
  obtain ⟨hl, hr', _⟩ := matrixResolvent_inverse_norm_of_separation A z r hr hsep
  let v : (Matrix I I ℂ)ˣ := ⟨matrixShift A z, matrixResolvent A z, hl, hr'⟩
  exact (Ring.inverse_unit v).symm

/-- Differentiation of an affine inverse in the L2 matrix norm. -/
theorem affine_ringInverse_hasDerivAt (M D : Matrix I I ℂ) (s : ℝ)
    (hunit : IsUnit (M+s • D)) :
    HasDerivAt (fun t : ℝ => Ring.inverse (M+t • D))
      (-(Ring.inverse (M+s • D))*D*Ring.inverse (M+s • D)) s := by
  have hd : HasDerivAt (fun t : ℝ => M+t • D) D s := by
    simpa only [id_eq,one_smul] using HasDerivAt.const_add M ((hasDerivAt_id s).smul_const D)
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit).comp_hasDerivAt s
    (by simpa only [hunit.unit_spec] using hd)
  simpa only [Function.comp_def, _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← Ring.inverse_unit hunit.unit, hunit.unit_spec, neg_mul] using hi

end Qatlib.Concepts.MatrixContour.ContourCalc
