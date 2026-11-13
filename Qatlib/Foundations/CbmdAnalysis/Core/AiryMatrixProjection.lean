/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AiryProjection
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMixture

/-!
# Matrix Airy projection and normalization

This module defines `airyMatrixProjection` by its convergent power series and identifies it with
`airyAi0` times `airyPropagator`. It transfers this normalization to scalar evaluations, matrix
actions, norms, and output ratios, connecting the normalized propagator with the Airy projection
used in [WangEtAl2026].

## Main statements

* `airyMatrixProjection_eq`: the matrix projection is a scalar multiple of the normalized
  propagator.
* `airyMatrixProjection_scalar`: scalar evaluation recovers `airyProjection`.
* `airyOutputRatio_normalization`: the original and normalized output ratios differ by
  `airyAi0`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- The Airy projection power series with coefficients `airyAi0 * airySeriesCoefficient n`
evaluated at `-(t ^ 3) • A`. -/
def airyMatrixProjection (A : E) (t : ℂ) : E :=
  ∑' n : ℕ, ((airyAi0 * airySeriesCoefficient n : ℝ) : ℂ) • (-(t ^ 3) • A) ^ n

/-- The series defining the matrix Airy projection is summable for every algebra element `A` and
complex time `t`. -/
theorem airyMatrixProjection_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => ((airyAi0 * airySeriesCoefficient n : ℝ) : ℂ) • (-(t ^ 3) • A) ^ n) := by
  simpa only [Complex.ofReal_mul, smul_smul] using!
    (airy_series_summable A t).const_smul (airyAi0 : ℂ)

omit [CompleteSpace E] in

/-- The matrix Airy projection equals `airyAi0` times the normalized Airy propagator. -/
theorem airyMatrixProjection_eq (A : E) (t : ℂ) :
    airyMatrixProjection A t = (airyAi0 : ℂ) • airyPropagator A t := by
  rw [airyMatrixProjection, airyPropagator, ← tsum_const_smul'']
  congr 1
  funext n
  rw [Complex.ofReal_mul, smul_smul]

omit [CompleteSpace E] in

/-- Multiplying the matrix Airy projection by the inverse of `airyAi0` gives the normalized Airy
propagator. -/
theorem airyMatrixProjection_normalized (A : E) (t : ℂ) :
    (airyAi0 : ℂ)⁻¹ • airyMatrixProjection A t = airyPropagator A t := by
  rw [airyMatrixProjection_eq, smul_smul, inv_mul_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.mpr airyAi0_pos.ne'

omit [CompleteSpace E] in

/-- The norm of the matrix Airy projection is `airyAi0` times the norm of the normalized
propagator. -/
theorem airyMatrixProjection_norm (A : E) (t : ℂ) :
    ‖airyMatrixProjection A t‖ = airyAi0 * ‖airyPropagator A t‖ := by
  rw [airyMatrixProjection_eq, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg airyAi0_pos.le]

end BanachAlgebra

/-- For the scalar argument `z ^ 3`, the matrix Airy projection at time `t` equals
`airyProjection (z * t)`. -/
theorem airyMatrixProjection_scalar (z t : ℂ) :
    airyMatrixProjection (z ^ 3) t = airyProjection (z * t) := by
  rw [airyMatrixProjection_eq, airyProjection_eq_series]
  simp only [airyPropagator, smul_eq_mul]
  congr 1
  congr 1
  funext n
  congr 2
  ring

/-- For nonnegative `γ` and `t`, the exponent `airyTimeScale t * sqrt (γ / 2)` equals `(2 / 3) *
sqrt (γ / 2 * t ^ 3)`. -/
theorem airyEnvelope_eq_paper {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    airyTimeScale t * Real.sqrt (γ / 2) = (2 / 3) * Real.sqrt (γ / 2 * t ^ 3) := by
  apply (sq_eq_sq₀ (mul_nonneg (airyTimeScale_nonneg ht) (Real.sqrt_nonneg _))
    (by positivity)).mp
  rw [mul_pow, airyTimeScale_sq ht, Real.sq_sqrt (by positivity),
    mul_pow, Real.sq_sqrt (by positivity)]
  ring

section Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The action of the matrix Airy projection on a vector is `airyAi0` times the action of the
normalized Airy propagator. -/
theorem airyMatrixProjection_apply (A : Matrix n n ℂ) (t : ℂ) (u : EuclideanSpace ℂ n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A t) u =
      (airyAi0 : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A t) u := by
  rw [airyMatrixProjection_eq, map_smul]
  rfl

/-- The norm of the projected output vector is `airyAi0` times the norm of the normalized
propagator output. -/
theorem airyMatrixProjection_apply_norm (A : Matrix n n ℂ) (t : ℂ) (u : EuclideanSpace ℂ n) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A t) u‖ =
      airyAi0 * ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A t) u‖ := by
  rw [airyMatrixProjection_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg airyAi0_pos.le]

/-- The input norm times the paper's exponential envelope, divided by the norm of the matrix
Airy projection output. -/
def airyOriginalOutputRatio (γ t : ℝ) (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) : ℝ :=
  ‖u‖ * Real.exp ((2 / 3) * Real.sqrt (γ / 2 * t ^ 3)) /
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A (t : ℂ)) u‖

/-- The input norm times the Airy time-scale exponential envelope, divided by the norm of the
normalized Airy propagator output. -/
def airyNormalizedOutputRatio (γ t : ℝ) (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) : ℝ :=
  ‖u‖ * Real.exp (airyTimeScale t * Real.sqrt (γ / 2)) /
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A (t : ℂ)) u‖

/-- For nonnegative `γ` and `t`, multiplying the original output ratio by `airyAi0` gives the
normalized output ratio. -/
theorem airyOutputRatio_normalization {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) :
    airyAi0 * airyOriginalOutputRatio γ t A u = airyNormalizedOutputRatio γ t A u := by
  unfold airyOriginalOutputRatio airyNormalizedOutputRatio
  rw [airyMatrixProjection_apply_norm, airyEnvelope_eq_paper hγ ht]
  field_simp [airyAi0_pos.ne']

end Matrix
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
