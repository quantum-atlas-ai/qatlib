/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CurveletLiu08.MainResults.ProbabilityCore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial variance and directional decomposition

This module defines the perpendicular component `perpPart` and the squared directional
quantities `orthVar` and `parVar`. For unit directions it proves orthogonality and a Pythagorean
identity, and it converts assumed fine-scale integral estimates into conditional-mean bounds.

These constructions accompany the results of [Liu2009].

## Main statements

* `orthVar_add_parVar`: decomposes the squared norm along a unit direction.
* `fineScale_prob_ge_of_subset`: compares a subset measure with the scale-cutoff probability.
* `source_theorem3`: normalizes the assumed radial variance integral bounds.

## References

* [Liu, 2009][Liu2009]
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace Qatlib.Papers.CurveletLiu08.MainResults

/-- The vector `x - ⟪θ, x⟫ • θ`, which is the perpendicular component of `x` when `θ` is a unit
vector. -/
def perpPart {n : ℕ} (θ x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (⟪θ, x⟫ : ℝ) • θ

/-- The squared norm of `perpPart θ b`, expressed as its inner product with itself. -/
def orthVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (⟪perpPart θ b, perpPart θ b⟫ : ℝ)

/-- The square of the real inner product of `θ` with `b`. -/
def parVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : ℝ := (⟪θ, b⟫ : ℝ) ^ 2

/-- For a unit direction, `perpPart θ b` is orthogonal to `θ`. -/
theorem perpPart_inner_self {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    (⟪θ, perpPart θ b⟫ : ℝ) = 0 := by
  have hθ2 : (⟪θ, θ⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]
    norm_num
  unfold perpPart
  rw [inner_sub_right, real_inner_smul_right, hθ2]
  ring

/-- For a unit direction, perpendicular variance is the squared norm minus the squared
directional inner product. -/
theorem orthVar_eq_norm_sq {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    orthVar b θ = ‖b‖ ^ 2 - (⟪θ, b⟫ : ℝ) ^ 2 := by
  unfold orthVar perpPart
  rw [real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, hθ, mul_one, sq_abs, real_inner_comm b θ]
  ring

/-- For a unit direction, the perpendicular and parallel variances sum to the squared norm. See
[Liu2009]. -/
theorem orthVar_add_parVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    orthVar b θ + parVar b θ = ‖b‖ ^ 2 := by
  rw [orthVar_eq_norm_sq b θ hθ, parVar]
  ring

/-- Perpendicular variance is nonnegative. -/
theorem orthVar_nonneg {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ orthVar b θ := by
  unfold orthVar
  rw [real_inner_self_eq_norm_sq]
  positivity

/-- Parallel variance is nonnegative. -/
theorem parVar_nonneg {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ parVar b θ := by
  unfold parVar
  positivity

/-- The real-valued measure of a subset of a finite-measure scale-cutoff event is bounded by
`PrScaleLe`. See [Liu2009]. -/
theorem fineScale_prob_ge_of_subset {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → ℝ) (η : ℝ) {s : Set Ω} (hsub : s ⊆ {ω | a ω ≤ η})
    (hfin : P {ω | a ω ≤ η} ≠ ∞) :
    P.real s ≤ PrScaleLe P a η :=
  measureReal_mono hsub hfin

/-- The assumed radial integral estimates yield the displayed bounds on conditional
perpendicular and parallel variances when the cutoff probability is positive. This is the
normalization step for Theorem 3 of [Liu2009]. -/
theorem source_theorem3
    (n : ℕ) (_hn : 4 ≤ n) (β : ℝ) (_hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → ℝ) (b θ : Ω → EuclideanSpace ℝ (Fin n))
    (η C₁ C₂ : ℝ) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hPr : 0 < PrScaleLe P a η)
    (horth : ∫ ω in {ω | a ω ≤ η}, orthVar (b ω) (θ ω) ∂P ≤
        η * β ^ 2 * (14300 + C₁ / (n : ℝ)) * PrScaleLe P a η)
    (hpar : ∫ ω in {ω | a ω ≤ η}, parVar (b ω) (θ ω) ∂P ≤
        β ^ 2 * (242 + C₂ / (n : ℝ)) * PrScaleLe P a η) :
    condExpect P a (fun ω => orthVar (b ω) (θ ω)) η ≤
        η * β ^ 2 * (14300 + C₁ / (n : ℝ)) ∧
    condExpect P a (fun ω => parVar (b ω) (θ ω)) η ≤
        β ^ 2 * (242 + C₂ / (n : ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact condExpect_le_of_setIntegral_le P a _ η _ hPr horth
  · exact condExpect_le_of_setIntegral_le P a _ η _ hPr hpar

end Qatlib.Papers.CurveletLiu08.MainResults
