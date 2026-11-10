/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AiryProjection
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMixture
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

def airyMatrixProjection (A : E) (t : ℂ) : E :=
  ∑' n : ℕ, ((airyAi0 * airySeriesCoefficient n : ℝ) : ℂ) • (-(t ^ 3) • A) ^ n

theorem airyMatrixProjection_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => ((airyAi0 * airySeriesCoefficient n : ℝ) : ℂ) • (-(t ^ 3) • A) ^ n) := by
  simpa only [Complex.ofReal_mul, smul_smul] using!
    (airy_series_summable A t).const_smul (airyAi0 : ℂ)

omit [CompleteSpace E] in

theorem airyMatrixProjection_eq (A : E) (t : ℂ) :
    airyMatrixProjection A t = (airyAi0 : ℂ) • airyPropagator A t := by
  rw [airyMatrixProjection, airyPropagator, ← tsum_const_smul'']
  congr 1
  funext n
  rw [Complex.ofReal_mul, smul_smul]

omit [CompleteSpace E] in

theorem airyMatrixProjection_normalized (A : E) (t : ℂ) :
    (airyAi0 : ℂ)⁻¹ • airyMatrixProjection A t = airyPropagator A t := by
  rw [airyMatrixProjection_eq, smul_smul, inv_mul_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.mpr airyAi0_pos.ne'

omit [CompleteSpace E] in

theorem airyMatrixProjection_norm (A : E) (t : ℂ) :
    ‖airyMatrixProjection A t‖ = airyAi0 * ‖airyPropagator A t‖ := by
  rw [airyMatrixProjection_eq, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg airyAi0_pos.le]

end BanachAlgebra

theorem airyMatrixProjection_scalar (z t : ℂ) :
    airyMatrixProjection (z ^ 3) t = airyProjection (z * t) := by
  rw [airyMatrixProjection_eq, airyProjection_eq_series]
  simp only [airyPropagator, smul_eq_mul]
  congr 1
  congr 1
  funext n
  congr 2
  ring

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

theorem airyMatrixProjection_apply (A : Matrix n n ℂ) (t : ℂ) (u : EuclideanSpace ℂ n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A t) u =
      (airyAi0 : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A t) u := by
  rw [airyMatrixProjection_eq, map_smul]
  rfl

theorem airyMatrixProjection_apply_norm (A : Matrix n n ℂ) (t : ℂ) (u : EuclideanSpace ℂ n) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A t) u‖ =
      airyAi0 * ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A t) u‖ := by
  rw [airyMatrixProjection_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg airyAi0_pos.le]

def airyOriginalOutputRatio (γ t : ℝ) (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) : ℝ :=
  ‖u‖ * Real.exp ((2 / 3) * Real.sqrt (γ / 2 * t ^ 3)) /
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyMatrixProjection A (t : ℂ)) u‖

def airyNormalizedOutputRatio (γ t : ℝ) (A : Matrix n n ℂ) (u : EuclideanSpace ℂ n) : ℝ :=
  ‖u‖ * Real.exp (airyTimeScale t * Real.sqrt (γ / 2)) /
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (airyPropagator A (t : ℂ)) u‖

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
