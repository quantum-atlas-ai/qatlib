/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.CurveletLiu08.MainResults

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type*} [MeasurableSpace I]

def curveletCoeff (v : I → H) (f : H) : I → ℝ := fun i => ⟪v i, f⟫

noncomputable def curveletSynthesis (v : I → H) (μ : Measure I) (c : I → ℝ) : H :=
  ∫ i, c i • v i ∂μ

structure IsCurveletFrame (V : Submodule ℝ H) (μ : Measure I) (v : I → H) : Prop where

  integrable : ∀ f : H, Integrable (fun i => (⟪v i, f⟫ : ℝ) • v i) μ

  synthesis_mem : ∀ c : I → ℝ, curveletSynthesis v μ c ∈ V

  gram : ∀ f ∈ V, ∀ g ∈ V, ∫ i, ⟪v i, f⟫ * ⟪v i, g⟫ ∂μ = ⟪f, g⟫

theorem inner_curveletSynthesis (v : I → H) (μ : Measure I) (c : I → ℝ)
    (hint : Integrable (fun i => c i • v i) μ) (g : H) :
    ⟪curveletSynthesis v μ c, g⟫ = ∫ i, c i * ⟪v i, g⟫ ∂μ := by
  rw [curveletSynthesis, real_inner_comm]
  rw [← innerSL_apply_apply ℝ g (∫ i, c i • v i ∂μ)]
  rw [← ContinuousLinearMap.integral_comp_comm (innerSL ℝ g) hint]
  apply integral_congr_ae
  filter_upwards with i
  rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]

theorem curvelet_reconstruction (V : Submodule ℝ H) (μ : Measure I) (v : I → H)
    (F : IsCurveletFrame V μ v) {f : H} (hf : f ∈ V) :
    curveletSynthesis v μ (curveletCoeff v f) = f := by
  have hmem : curveletSynthesis v μ (curveletCoeff v f) ∈ V := F.synthesis_mem _
  have hxV : curveletSynthesis v μ (curveletCoeff v f) - f ∈ V := V.sub_mem hmem hf
  have hpair : ∀ g ∈ V, ⟪curveletSynthesis v μ (curveletCoeff v f), g⟫ = ⟪f, g⟫ := by
    intro g hg
    rw [inner_curveletSynthesis v μ (curveletCoeff v f) (F.integrable f) g]
    exact F.gram f hf g hg
  have hx0 : curveletSynthesis v μ (curveletCoeff v f) - f = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    rw [inner_sub_left, hpair _ hxV, sub_self]
  exact sub_eq_zero.mp hx0

theorem curvelet_parseval (V : Submodule ℝ H) (μ : Measure I) (v : I → H)
    (F : IsCurveletFrame V μ v) {f : H} (hf : f ∈ V) :
    ∫ i, (⟪v i, f⟫ : ℝ) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := F.gram f hf f hf
  rw [← real_inner_self_eq_norm_sq f, ← h]
  apply integral_congr_ae
  filter_upwards with i
  ring

end Qatlib.Papers.CurveletLiu08.MainResults
