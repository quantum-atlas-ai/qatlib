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

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace Qatlib.Papers.CurveletLiu08.MainResults

def perpPart {n : ℕ} (θ x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (⟪θ, x⟫ : ℝ) • θ

def orthVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (⟪perpPart θ b, perpPart θ b⟫ : ℝ)

def parVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : ℝ := (⟪θ, b⟫ : ℝ) ^ 2

theorem perpPart_inner_self {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    (⟪θ, perpPart θ b⟫ : ℝ) = 0 := by
  have hθ2 : (⟪θ, θ⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]
    norm_num
  unfold perpPart
  rw [inner_sub_right, real_inner_smul_right, hθ2]
  ring

theorem orthVar_eq_norm_sq {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    orthVar b θ = ‖b‖ ^ 2 - (⟪θ, b⟫ : ℝ) ^ 2 := by
  unfold orthVar perpPart
  rw [real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, hθ, mul_one, sq_abs, real_inner_comm b θ]
  ring

theorem orthVar_add_parVar {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    orthVar b θ + parVar b θ = ‖b‖ ^ 2 := by
  rw [orthVar_eq_norm_sq b θ hθ, parVar]
  ring

theorem orthVar_nonneg {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ orthVar b θ := by
  unfold orthVar
  rw [real_inner_self_eq_norm_sq]
  positivity

theorem parVar_nonneg {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ parVar b θ := by
  unfold parVar
  positivity

theorem fineScale_prob_ge_of_subset {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → ℝ) (η : ℝ) {s : Set Ω} (hsub : s ⊆ {ω | a ω ≤ η})
    (hfin : P {ω | a ω ≤ η} ≠ ∞) :
    P.real s ≤ PrScaleLe P a η :=
  measureReal_mono hsub hfin

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
