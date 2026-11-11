/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayerL2Multiplier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2


/-! A continuous frame produces an actual L2 analysis operator. Its weighted
moments are proved from the integral definition, and its isometry follows
from mass I. Polygon Gram rows still need to be assembled into this frame. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped ENNReal InnerProduct
variable {X E : Type} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Construction for analysis Linear in the double layer l2 frame model. -/
def analysisLinear (w : C(X,E)) : E →ₗ[ℂ] C(X,ℂ) where
  toFun x := ⟨fun t => inner ℂ (w t) x,w.continuous.inner continuous_const⟩
  map_add' x y := by
    ext1 t
    change inner ℂ (w t) (x+y)=inner ℂ (w t) x+inner ℂ (w t) y
    exact inner_add_right _ _ _
  map_smul' c x := by
    ext1 t
    change inner ℂ (w t) (c • x)=c • inner ℂ (w t) x
    rw [inner_smul_right]
    rfl

/-- Construction for analysis C in the double layer l2 frame model. -/
def analysisC (w : C(X,E)) : E →L[ℂ] C(X,ℂ) :=
  (analysisLinear w).mkContinuous ‖w‖ (fun x => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg w) (norm_nonneg x))).mpr
    intro t
    exact (norm_inner_le_norm (𝕜 := ℂ) (w t) x).trans
      (mul_le_mul_of_nonneg_right (w.norm_coe_le_norm t) (norm_nonneg x)))

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Construction for analysis in the double layer l2 frame model. -/
def analysis (w : C(X,E)) : E →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ) ∘L analysisC w

/-- The identity or estimate `analysis_ae` holds with the displayed separation, geometry and norm hypotheses. -/
theorem analysis_ae (w : C(X,E)) (x : E) : analysis μ w x=ᵐ[μ] fun t => inner ℂ (w t) x :=
  ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ) (analysisC w x)

variable [CompleteSpace E] [SecondCountableTopology X]

/-- The identity or estimate `weighted_inner` holds with the displayed separation, geometry and norm hypotheses. -/
theorem weighted_inner (w : C(X,E)) (g : C(X,ℂ)) (x y : E) :
    inner ℂ (analysis μ w x) (multiplication μ g (analysis μ w y))=
      inner ℂ x ((∫ t,g t • rankOne ℂ (w t) (w t) ∂μ) y) := by
  have hRank : Continuous (fun t => rankOne ℂ (w t) (w t)) := by
    simpa only [Function.comp_apply,toSpanSingletonLIE_apply,rankOne_def'] using
      ((toSpanSingletonLIE ℂ E).continuous.comp w.continuous).clm_comp
        ((innerSL ℂ).continuous.comp w.continuous)
  let F : C(X,E →L[ℂ] E) := ⟨fun t => g t • rankOne ℂ (w t) (w t),g.continuous.smul hRank⟩
  have hF : Integrable (fun t => g t • rankOne ℂ (w t) (w t)) μ :=
    memLp_one_iff_integrable.mp (F.memLp (p := 1) (μ := μ) ℂ)
  let L : (E →L[ℂ] E) →L[ℂ] ℂ := (innerSL ℂ x) ∘L ContinuousLinearMap.apply ℂ E y
  rw [L2.inner_def]
  calc
    _ = ∫ t,inner ℂ x ((g t • rankOne ℂ (w t) (w t)) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [analysis_ae μ w x,analysis_ae μ w y,
        multiplication_ae μ g (analysis μ w y)] with t hx hy hm
      rw [hx,hm,hy]
      simp only [smul_apply,rankOne_apply,inner_smul_right,RCLike.inner_apply']
      rw [← inner_conj_symm (𝕜 := ℂ) (x := x) (y := w t)]
      ring
    _ = _ := L.integral_comp_comm hF

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2

namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped ENNReal InnerProduct
variable {X E : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The identity or estimate `analysis_norm` holds with the displayed separation, geometry and norm hypotheses. -/
theorem analysis_norm (w : C(X,E))
    (hMass : (∫ t,rankOne ℂ (w t) (w t) ∂μ)=1) (x : E) : ‖analysis μ w x‖=‖x‖ := by
  have hi := weighted_inner μ w (1 : C(X,ℂ)) x x
  simp only [multiplication_one,one_apply,ContinuousMap.one_apply,one_smul,hMass] at hi
  have hs : ‖analysis μ w x‖^2=‖x‖^2 := by
    calc
      _ = (inner ℂ (analysis μ w x) (analysis μ w x)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ x x).re := congrArg Complex.re hi
      _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (analysis μ w x),norm_nonneg x]

/-- The identity or estimate `all_power_moment` holds with the displayed separation, geometry and norm hypotheses. -/
theorem all_power_moment (w : C(X,E)) (g : C(X,ℂ)) (n : ℕ) :
    (analysis μ w)† ∘L (((dilationContraction μ g)†)^n) ∘L analysis μ w=
      ∫ t,(g t)^n • rankOne ℂ (w t) (w t) ∂μ := by
  rw [dilationContraction,adjoint_adjoint,multiplication_pow]
  ext1 y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (((analysis μ w)†) (multiplication μ (g^n) (analysis μ w y)))=_
  rw [adjoint_inner_right]
  simpa only [ContinuousMap.pow_apply] using weighted_inner μ w (g^n) x y

/-- The identity or estimate `frame_dilation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem frame_dilation (w : C(X,E)) (g : C(X,ℂ))
    (hMass : (∫ t,rankOne ℂ (w t) (w t) ∂μ)=1) (hg : ∀ t,‖g t‖≤1) :
    (∀ x,‖analysis μ w x‖=‖x‖) ∧ ‖dilationContraction μ g‖≤1 ∧
      ∀ n : ℕ,(analysis μ w)† ∘L (((dilationContraction μ g)†)^n) ∘L analysis μ w=
        ∫ t,(g t)^n • rankOne ℂ (w t) (w t) ∂μ := by
  exact ⟨analysis_norm μ w hMass,dilationContraction_norm μ g hg,all_power_moment μ w g⟩

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
