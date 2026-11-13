/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelPoleCoefficients
import Qatlib.Foundations.CbmdAnalysis.Core.KernelPoleSet
import Qatlib.Foundations.CbmdAnalysis.Core.AnalyticRegulator
import Qatlib.Foundations.CbmdAnalysis.Core.KernelLCU
import Qatlib.Foundations.CbmdAnalysis.Core.KernelContourLimit

/-!
# Finite circle identity for the integer kernel

This module evaluates the integer-kernel integral over a half-grid circle enclosing all
auxiliary poles. The residue sum consists of the target value at `-i`, the negative finite
real-sampling sum, and the auxiliary correction.

`integerContour_circle_identity_normalized` divides by `2πi` to expose the finite sampling
identity used in [WangEtAl2026].

## Main statements

* `integerContour_circle_identity`: evaluates the finite circle integral.
* `integerContour_circle_identity_normalized`: states the normalized identity.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open Metric Complex
open scoped BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- For positive spacing and an entire `U`, a half-grid circle of radius greater than `m + 2`
has integral `2πi` times the target value minus the finite LCU sum plus the auxiliary
correction [WangEtAl2026]. -/
theorem integerContour_circle_identity (m : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : (m : ℝ) + 2 < halfGridRadius a n) (U : ℂ → E) (hU : Differentiable ℂ U) :
    (∮ z in C(0, halfGridRadius a n), integerContourIntegrand m a U z) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        (U (-Complex.I) - integerLCUSum m a n U + integerAuxiliaryCorrection m a U) := by
  classical
  let c : ℂ := ((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)
  have hR0 : 0 ≤ halfGridRadius a n := by unfold halfGridRadius; positivity
  have hinside := integerPoleSet_inside m ha n hR
  have hzeros := integerContourDenominator_disk_zeros m ha n
  have hsimple : ∀ p ∈ integerPoleSet m a n, deriv (integerContourDenominator m a) p ≠ 0 := by
    intro p hp
    have hz : integerContourDenominator m a p = 0 :=
      (hzeros p (ball_subset_closedBall (hinside p hp))).mpr hp
    exact integerContourDenominator_deriv_ne_zero_of_eq_zero m ha p hz
  have hF : Differentiable ℂ (fun z => c • U z) := (differentiable_const c).smul hU
  have hC := circleIntegral_analytic_regulator (integerPoleSet m a n) hR0
    (fun z => c • U z) (integerContourDenominator m a) hF.diffContOnCl
    (integerContourDenominator_differentiable m a).diffContOnCl hinside hzeros hsimple
  have heq : (fun z => integerContourIntegrand m a U z) =
      (fun z => (integerContourDenominator m a z)⁻¹ • (c • U z)) := by
    funext z
    exact integerContourIntegrand_eq_denominator m a U z
  rw [heq, hC]
  congr 1
  have hcoef (p : ℂ) : (deriv (integerContourDenominator m a) p)⁻¹ • (c • U p) =
      (c / deriv (integerContourDenominator m a) p) • U p := by
    rw [smul_smul]
    congr 1
    ring
  simp_rw [hcoef]
  rw [integerPoleSet_sum m ha n]
  have hrow : (∑ r ∈ Finset.Icc (-(m : ℤ)) m,
      (c / deriv (integerContourDenominator m a) ((r : ℂ) + Complex.I)) • U ((r : ℂ) + Complex.I)) =
      ∑ r ∈ Finset.Icc (-(m : ℤ)) m,
        integerRowResidueCoefficient m a r • U ((r : ℂ) + Complex.I) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [show c / deriv (integerContourDenominator m a) ((r : ℂ) + Complex.I) =
      integerRowResidueCoefficient m a r from integerContour_coefficient_row m ha r hr]
  rw [hrow]
  dsimp [c]
  rw [integerContour_coefficient_neg_I m ha, one_smul, integerContour_coefficient_top m ha]
  simp_rw [integerContour_coefficient_lattice m ha, neg_smul]
  rw [Finset.sum_neg_distrib]
  unfold integerLCUSum integerSample integerAuxiliaryCorrection
  abel

/-- After division by `2πi`, the integer-kernel circle integral equals `U (-i) - integerLCUSum m
a n U + integerAuxiliaryCorrection m a U` under the stated enclosure and differentiability
hypotheses. -/
theorem integerContour_circle_identity_normalized (m : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : (m : ℝ) + 2 < halfGridRadius a n) (U : ℂ → E) (hU : Differentiable ℂ U) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      (∮ z in C(0, halfGridRadius a n), integerContourIntegrand m a U z) =
        U (-Complex.I) - integerLCUSum m a n U + integerAuxiliaryCorrection m a U := by
  rw [integerContour_circle_identity m ha n hR U hU, smul_smul, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
