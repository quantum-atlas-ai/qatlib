/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

/-! # The same binomial coordinate-word bound for real phase products -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of real Quaternion CLM in the Hopf Atlas construction. -/
def realQuaternionCLM : ℝ →L[ℝ] ℍ := ContinuousLinearMap.toSpanSingleton ℝ (1 : ℍ)

/-- Original `realQuaternionCLM_norm` guarantee for the `ScalarWordProduct` construction; the complete source hypotheses are retained. -/
theorem realQuaternionCLM_norm (r : ℝ) : ‖realQuaternionCLM r‖=‖r‖ := by
  simp [realQuaternionCLM]

/-- Original `realQuaternionCLM_mul` guarantee for the `ScalarWordProduct` construction; the complete source hypotheses are retained. -/
theorem realQuaternionCLM_mul (a b : ℝ) :
    realQuaternionCLM (a*b)=realQuaternionCLM a*realQuaternionCLM b := by
  simp [realQuaternionCLM,smul_smul,mul_comm]

/-- Real phase products use the proved quaternion product estimate through
an isometric real embedding; no operator-norm strengthening is assumed. -/
theorem spatialWordPartial_real_mul_norm_le (f g : SpatialPoint → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (F G : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hF : ∀ j ≤ w.length, 0 ≤ F j) (hG : ∀ j ≤ w.length, 0 ≤ G j)
    (hfB : ∀ u : List (Fin 3), u.length ≤ w.length → ‖spatialWordPartial f u x‖ ≤ F u.length)
    (hgB : ∀ u : List (Fin 3), u.length ≤ w.length → ‖spatialWordPartial g u x‖ ≤ G u.length) :
    ‖spatialWordPartial (fun y => f y*g y) w x‖ ≤ wordProductMajorant F G w.length := by
  have hfE := realQuaternionCLM.contDiff.comp hf
  have hgE := realQuaternionCLM.contDiff.comp hg
  have hfEB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (fun y => realQuaternionCLM (f y)) u x‖ ≤ F u.length := by
    intro u hu
    rw [spatialWordPartial_clm realQuaternionCLM f hf,realQuaternionCLM_norm]
    exact hfB u hu
  have hgEB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (fun y => realQuaternionCLM (g y)) u x‖ ≤ G u.length := by
    intro u hu
    rw [spatialWordPartial_clm realQuaternionCLM g hg,realQuaternionCLM_norm]
    exact hgB u hu
  have h := spatialWordPartial_mul_norm_le
    (fun y => realQuaternionCLM (f y)) (fun y => realQuaternionCLM (g y))
    hfE hgE F G w x hF hG hfEB hgEB
  have heq : (fun y => realQuaternionCLM (f y)*realQuaternionCLM (g y))=
      fun y => realQuaternionCLM (f y*g y) := funext (fun y => (realQuaternionCLM_mul (f y) (g y)).symm)
  rw [heq,spatialWordPartial_clm realQuaternionCLM _ (hf.mul hg),realQuaternionCLM_norm] at h
  exact h

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
