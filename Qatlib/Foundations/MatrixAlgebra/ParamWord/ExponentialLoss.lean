/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.HermitianSlots
import Qatlib.Foundations.MatrixAlgebra.ParamWord.WordSmooth
import Qatlib.Foundations.MatrixAlgebra.ParamWord.LossBounds
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

def matrixStateCLM (ψ : EuclideanSpace ℂ I) : Matrix I I ℂ→L[ℝ]EuclideanSpace ℂ I :=
  ((((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ I) ψ).toLinearMap).restrictScalars ℝ).comp
    ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)).toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ)).mkContinuous ‖ψ‖ (fun A => by
      change ‖(Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A ψ‖≤‖ψ‖*‖A‖
      simpa only [Matrix.l2_opNorm_toEuclideanCLM,mul_comm] using
          ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A).le_opNorm ψ)

omit [Nonempty I] in

theorem matrixStateCLM_apply (ψ : EuclideanSpace ℂ I) (A : Matrix I I ℂ) :
    matrixStateCLM ψ A=(Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A ψ := rfl

omit [Nonempty I] in

theorem matrixStateCLM_norm (ψ : EuclideanSpace ℂ I) : ‖matrixStateCLM ψ‖≤‖ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  rw [matrixStateCLM_apply]
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,mul_comm] using
      ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A).le_opNorm ψ

def exponentialWord {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : Matrix I I ℂ :=
  paramWord (fun j => expSlot (G j) (W j) j) (List.finRange K) θ

def exponentialWordD {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]Matrix I I ℂ :=
  paramWordD (fun j => expSlot (G j) (W j) j) (fun j => expSlotD (G j) (W j) j) (List.finRange K) θ

def wordState {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℂ I :=
  matrixStateCLM ψ (exponentialWord G W θ)

def wordStateD {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]EuclideanSpace ℂ I :=
  (matrixStateCLM ψ).comp (exponentialWordD G W θ)

def observableCLM (O : Matrix I I ℂ) : EuclideanSpace ℂ I→L[ℝ]EuclideanSpace ℂ I :=
  ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) O).restrictScalars ℝ

def wordLoss {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  (inner ℂ (wordState G W ψ θ) ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) O (wordState G W ψ θ))).re

def wordLossD {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]ℝ :=
  expectationD (observableCLM O) (wordState G W ψ) (wordStateD G W ψ) θ

omit [Nonempty I] in

theorem wordLoss_eq_expectation {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) : wordLoss G W O ψ=expectation (observableCLM O) (wordState G W ψ) := rfl

omit [Nonempty I] in

theorem exponentialWord_hasFDerivAt {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (exponentialWord G W) (exponentialWordD G W θ) θ :=
  paramWord_hasFDerivAt _ _ (fun j x => expSlot_hasFDerivAt (G j) (W j) j x) _ θ

theorem exponentialWord_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖exponentialWord G W θ‖≤1 :=
  paramWord_norm _ (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le) _ θ

theorem exponentialWordD_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖exponentialWordD G W θ‖≤K := by
  exact (paramWordD_norm _ _
    (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le)
    (fun j x => expSlotD_norm (G j) (W j) j (hG j) (hGn j) (hW j) x) _ θ).trans_eq (by simp)

theorem exponentialWordD_lipschitz {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ η : EuclideanSpace ℝ (Fin K)) : ‖exponentialWordD G W θ-exponentialWordD G W η‖≤(K:ℝ)^2*‖θ-η‖ := by
  have h := paramWordD_lipschitz_bound (fun j => expSlot (G j) (W j) j)
    (fun j => expSlotD (G j) (W j) j)
    (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le)
    (fun j x => expSlotD_norm (G j) (W j) j (hG j) (hGn j) (hW j) x)
    (fun j x => expSlot_hasFDerivAt (G j) (W j) j x)
    (fun j x y => by simpa only [NNReal.coe_one,one_mul] using
      (expSlot_lipschitz (G j) (W j) j (hG j) (hGn j) (hW j)).norm_sub_le x y)
    (fun j x y => expSlotD_lipschitz (G j) (W j) j (hG j) (hGn j) (hW j) x y)
    (List.finRange K) θ η
  simpa only [List.length_finRange] using! h

omit [Nonempty I] in

theorem wordState_hasFDerivAt {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : HasFDerivAt (wordState G W ψ) (wordStateD G W ψ θ) θ :=
  (matrixStateCLM ψ).hasFDerivAt.comp θ (exponentialWord_hasFDerivAt G W θ)

theorem wordState_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖wordState G W ψ θ‖≤1 := by
  calc
    _ ≤ ‖matrixStateCLM ψ‖*‖exponentialWord G W θ‖ := (matrixStateCLM ψ).le_opNorm _
    _ ≤ 1*1 := mul_le_mul ((matrixStateCLM_norm ψ).trans_eq hψ)
      (exponentialWord_norm G W hG hW θ) (norm_nonneg _) zero_le_one
    _ = _ := one_mul 1

theorem wordStateD_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1)
    (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (θ : EuclideanSpace ℝ (Fin K)) :
    ‖wordStateD G W ψ θ‖≤K := by
  calc
    _ ≤ ‖matrixStateCLM ψ‖*‖exponentialWordD G W θ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*K := mul_le_mul ((matrixStateCLM_norm ψ).trans_eq hψ)
      (exponentialWordD_norm G W hG hGn hW θ) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem wordStateD_lipschitz {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1)
    (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (θ η : EuclideanSpace ℝ (Fin K)) :
    ‖wordStateD G W ψ θ-wordStateD G W ψ η‖≤(K:ℝ)^2*‖θ-η‖ := by
  have he : wordStateD G W ψ θ-wordStateD G W ψ η=
      (matrixStateCLM ψ).comp (exponentialWordD G W θ-exponentialWordD G W η) := by
    ext v
    simp [wordStateD]
  rw [he]
  calc
    _ ≤ ‖matrixStateCLM ψ‖*‖exponentialWordD G W θ-exponentialWordD G W η‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*((K:ℝ)^2*‖θ-η‖) :=
      mul_le_mul ((matrixStateCLM_norm ψ).trans_eq hψ) (exponentialWordD_lipschitz G W hG hGn hW θ η)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end Qatlib.Foundations.MatrixAlgebra.ParamWord
