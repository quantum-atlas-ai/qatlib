/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.ExponentialLoss
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix.Norms.L2Operator RightActions
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
local instance : CStarAlgebra (Matrix I I ℂ) where
local instance : NormedAlgebra ℝ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ I) := InnerProductSpace.complexToReal

omit [Nonempty I] in

theorem observableCLM_norm (O : Matrix I I ℂ) : ‖observableCLM O‖=‖O‖ := by
  rw [observableCLM,ContinuousLinearMap.norm_restrictScalars,Matrix.l2_opNorm_toEuclideanCLM]

theorem wordState_lipschitz {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1)
    (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) : LipschitzWith (K:NNReal) (wordState G W ψ) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
      (fun θ => (wordState_hasFDerivAt G W ψ θ).differentiableAt)
  intro θ
  change ‖fderiv ℝ (wordState G W ψ) θ‖≤(K:ℝ)
  rw [(wordState_hasFDerivAt G W ψ θ).fderiv]
  exact wordStateD_norm G W ψ hψ hG hGn hW θ

omit [Nonempty I] in

theorem wordLoss_hasFDerivAt {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (wordLoss G W O ψ) (wordLossD G W O ψ θ) θ := by
  rw [wordLoss_eq_expectation]
  exact expectation_hasFDerivAt _ _ _ (wordState_hasFDerivAt G W ψ) θ

theorem wordLoss_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian)
    (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (hO : ‖O‖≤1) (θ : EuclideanSpace ℝ (Fin K)) :
    ‖wordLoss G W O ψ θ‖≤1 := by
  rw [wordLoss_eq_expectation]
  exact expectation_abs_le _ _ ((observableCLM_norm O).trans_le hO)
      (wordState_norm G W ψ hψ hG hW) θ

theorem wordLoss_fderiv_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian)
    (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (hO : ‖O‖≤1)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖fderiv ℝ (wordLoss G W O ψ) θ‖≤2*(K:ℝ) := by
  rw [(wordLoss_hasFDerivAt G W O ψ θ).fderiv]
  exact expectationD_norm _ _ _ ((observableCLM_norm O).trans_le hO)
    (wordState_norm G W ψ hψ hG hW) K (Nat.cast_nonneg _)
    (wordStateD_norm G W ψ hψ hG hGn hW) θ

theorem wordLoss_fderiv_lipschitz {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian)
    (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (hO : ‖O‖≤1)
    (θ η : EuclideanSpace ℝ (Fin K)) :
    ‖fderiv ℝ (wordLoss G W O ψ) θ-fderiv ℝ (wordLoss G W O ψ) η‖≤(4*(K:ℝ)^2)*‖θ-η‖ := by
  rw [(wordLoss_hasFDerivAt G W O ψ θ).fderiv,(wordLoss_hasFDerivAt G W O ψ η).fderiv]
  have h := expectationD_lipschitz_bound (observableCLM O) (wordState G W ψ) (wordStateD G W ψ)
    ((observableCLM_norm O).trans_le hO) (wordState_norm G W ψ hψ hG hW)
    K ((K:ℝ)^2) (Nat.cast_nonneg _) (sq_nonneg _)
    (wordStateD_norm G W ψ hψ hG hGn hW)
    (fun x y => (wordState_lipschitz G W ψ hψ hG hGn hW).norm_sub_le x y)
    (wordStateD_lipschitz G W ψ hψ hG hGn hW) θ η
  convert! h using 1
  ring

theorem wordLoss_fderiv_continuous {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian)
    (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (hO : ‖O‖≤1) :
    Continuous (fderiv ℝ (wordLoss G W O ψ)) := by
  have hl : LipschitzWith (⟨4*(K:ℝ)^2,by positivity⟩:NNReal) (fderiv ℝ (wordLoss G W O ψ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    simpa only [dist_eq_norm] using! wordLoss_fderiv_lipschitz G W O ψ hψ hG hGn hW hO θ η
  exact hl.continuous

theorem actual_word_loss_contract {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian)
    (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (hO : ‖O‖≤1) :
    Differentiable ℝ (wordLoss G W O ψ) ∧ Continuous (fderiv ℝ (wordLoss G W O ψ)) ∧
    (∀θ,‖wordLoss G W O ψ θ‖≤1) ∧
    (∀θ,‖fderiv ℝ (wordLoss G W O ψ) θ‖≤2*(K:ℝ)) ∧
    (∀θ η,‖fderiv ℝ (wordLoss G W O ψ) θ-fderiv ℝ (wordLoss G W O ψ) η‖≤(4*(K:ℝ)^2)*‖θ-η‖) :=
  ⟨fun θ => (wordLoss_hasFDerivAt G W O ψ θ).differentiableAt,
    wordLoss_fderiv_continuous G W O ψ hψ hG hGn hW hO,
    wordLoss_norm G W O ψ hψ hG hW hO,
    wordLoss_fderiv_norm G W O ψ hψ hG hGn hW hO,
    wordLoss_fderiv_lipschitz G W O ψ hψ hG hGn hW hO⟩
end Qatlib.Foundations.MatrixAlgebra.ParamWord
