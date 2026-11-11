/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEnergy
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianZero

/-!
# Special physical Gaussian correlation cases

For unit input vectors, inner product one or minus one forces the corresponding endpoint value
of `rawExpectation`. Applied to physical fit vectors, these results and the orthogonal case
evaluate the expected rounded dot product when `tParam` is zero, one, or minus one. See
[CrostaSaubanereHuber2026].

## Main statements

* `physical_expected_dot_zero`: evaluates the expected dot product at zero physical correlation.
* `physical_expected_dot_one`: evaluates it at correlation one.
* `physical_BOV_zero`: identifies the zero case with the rank-three BOV kernel.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

/-- Two unit vectors with inner product one have raw rounded expectation one. -/
theorem rawExpectation_inner_one {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (h : inner ℝ u v=1) : rawExpectation u v=1 := by
  have hz : ‖u-v‖=0 := by nlinarith [norm_sub_sq_real u v,norm_nonneg (u-v)]
  have he : u=v := sub_eq_zero.mp (norm_eq_zero.mp hz)
  rw [← he,rawExpectation_eq,matrixExpectation_self u hu]

/-- Two unit vectors with inner product minus one have raw rounded expectation minus one. -/
theorem rawExpectation_inner_neg_one {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (h : inner ℝ u v= -1) : rawExpectation u v= -1 := by
  have hz : ‖u+v‖=0 := by nlinarith [norm_add_sq_real u v,norm_nonneg (u+v)]
  have he : v= -u := eq_neg_of_add_eq_zero_right (norm_eq_zero.mp hz)
  rw [he,rawExpectation_eq,matrixExpectation_neg u hu]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- For distinct sites with `tParam = 0`, the expected dot product of the physically rounded
vectors is zero. -/
theorem physical_expected_dot_zero (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) (ht : tParam ρ i j=0) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a ∂rawMatrixLaw (Fin 2 × MomentIndex n))=0 := by
  rw [physical_dot_expectation,rawExpectation_eq]
  exact matrixExpectation_orthogonal _ _ ((physicalFitEuclidean_dot n ρ hρ htr i j hij).trans ht)

/-- For distinct sites with `tParam = 1`, the expected dot product of the physically rounded
vectors is one. -/
theorem physical_expected_dot_one (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) (ht : tParam ρ i j=1) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a ∂rawMatrixLaw (Fin 2 × MomentIndex n))=1 := by
  rw [physical_dot_expectation]
  exact rawExpectation_inner_one _ _ (physicalFitEuclidean_unit n ρ hρ htr i) (physicalFitEuclidean_unit n ρ hρ htr j)
    ((physicalFitEuclidean_dot n ρ hρ htr i j hij).trans ht)

/-- For distinct sites with `tParam = -1`, the expected dot product of the physically rounded
vectors is minus one. -/
theorem physical_expected_dot_neg_one (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) (ht : tParam ρ i j= -1) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a ∂rawMatrixLaw (Fin 2 × MomentIndex n))= -1 := by
  rw [physical_dot_expectation]
  exact rawExpectation_inner_neg_one _ _ (physicalFitEuclidean_unit n ρ hρ htr i) (physicalFitEuclidean_unit n ρ hρ htr j)
    ((physicalFitEuclidean_dot n ρ hρ htr i j hij).trans ht)

/-- For distinct sites with zero physical correlation, the expected rounded dot product equals
`bovThreeKernel` evaluated at `tParam`. -/
theorem physical_BOV_zero (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) (ht : tParam ρ i j=0) :
    (∫ R : Fin 3 → Fin 2 × MomentIndex n → ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a ∂rawMatrixLaw (Fin 2 × MomentIndex n))=
      bovThreeKernel (tParam ρ i j) := by
  rw [physical_expected_dot_zero n ρ hρ htr i j hij ht,ht,bovThreeKernel_zero]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
