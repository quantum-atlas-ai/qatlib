/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift
public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexScale
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.EmptyBoundary

@[expose] public section


/-! # Actual Gaussian translation and boundary diagnostics

Fixed arXiv:1011.3245v1, Lemma 48. The general shift proof is reused through
its shared mathematical layer. Product densities have actual unit mass;
no normalization or final probability statement is a supplied hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.Gaussian
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- The actual shifted complex Gaussian density in the immutable original target. -/
def shiftDensity (v z : ℂ) : ℝ := Real.pi⁻¹ * Real.exp (-Complex.normSq (z-v))

/-- The exact original Euclidean-displacement Gaussian translation target. -/
theorem shiftBound (N : ℕ) (v : Fin N → ℂ) :
    (1/2) * ∫ x : Fin N → ℂ,
      |∏ i, shiftDensity (v i) (x i) - ∏ i, loGaussianDensity (x i)| ∂volume ≤
        Real.sqrt (∑ i, Complex.normSq (v i)) :=
  Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.shiftBound N v

/-- The exact original variance-scaling target, with its full positive error domain. -/
theorem scalingBound (N : ℕ) (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1) :
    (1/2) * ∫ x : Fin N → ℂ,
      |∏ i, ((1-eps)^2)⁻¹ * loGaussianDensity (x i / ((1-eps : ℝ) : ℂ))
        - ∏ i, loGaussianDensity (x i)| ∂volume ≤ 2*(N : ℝ)*eps :=
  Qatlib.Foundations.ProbabilityCore.Concentration.ComplexScale.scalingBound N h0 h1

/-- The actual Gaussian matrix density integrates to one in every finite matrix dimension. -/
theorem matrixMass (n : ℕ) :
    (∫ X : Fin n → Fin n → ℂ, loGaussianMatDensity n X ∂volume) = 1 := by
  change (∫ X : Fin n → Fin n → ℂ,
    ∏ i, Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.prodDensity n (X i)) = 1
  rw [integral_fintype_prod_volume_eq_prod]
  simp [Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.prodMass]

/-- A nonpositive threshold gives the entire actual nonnegative permanent random variable event. -/
theorem negativeEvent (n : ℕ) {alpha : ℝ} (ha : alpha ≤ 0) :
    EmptyBoundary.permProb n alpha = 1 := by
  unfold EmptyBoundary.permProb
  have hx (X : Fin n → Fin n → ℂ) : alpha ≤ EmptyBoundary.permMomentVar X :=
    ha.trans (div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))
  simp_rw [ite_eq_left (hx _), one_mul]
  exact matrixMass n

/-- Even positive dimension cannot repair the literal old weak bound without a threshold domain. -/
theorem positiveGap : ¬(EmptyBoundary.permProb 1 (-1) > (1-(-1 : ℝ))^2 / ((1 : ℝ)+1)) := by
  rw [negativeEvent 1 (by norm_num)]
  norm_num

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.Gaussian
