/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.HermitianSlots
import Qatlib.Foundations.MatrixAlgebra.ParamWord.WordSmooth
import Qatlib.Foundations.MatrixAlgebra.ParamWord.LossBounds

/-!
# Exponential circuit words, states, and expectation losses

`exponentialWord` forms the ordered product of parameterized matrix-exponential slots, and
`wordState` applies it to a complex Euclidean state. `wordLoss` takes the real part of the
resulting observable expectation, with explicit Fréchet derivatives for the word and state maps.

Under Hermitian-generator and unitary-gate hypotheses, the module derives word and state norm
bounds, derivative bounds proportional to `K`, and derivative Lipschitz bounds proportional to
`K²`. These constructions support the parameterized circuit losses of [TranEtAl2026].

## Main statements

* `exponentialWord_hasFDerivAt`: Derivative of the ordered exponential circuit.
* `wordState_hasFDerivAt`: Derivative of the evolved state.
* `wordStateD_lipschitz`: State derivative Lipschitz estimate.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

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

/-- The real continuous linear map sending a matrix to its action on the fixed state `ψ`. -/
def matrixStateCLM (ψ : EuclideanSpace ℂ I) : Matrix I I ℂ→L[ℝ]EuclideanSpace ℂ I :=
  ((((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ I) ψ).toLinearMap).restrictScalars ℝ).comp
    ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)).toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ)).mkContinuous ‖ψ‖ (fun A => by
      change ‖(Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A ψ‖≤‖ψ‖*‖A‖
      simpa only [Matrix.l2_opNorm_toEuclideanCLM,mul_comm] using
          ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A).le_opNorm ψ)

omit [Nonempty I] in

/-- The map `matrixStateCLM ψ` acts by the Euclidean continuous linear operator represented by
the matrix. -/
theorem matrixStateCLM_apply (ψ : EuclideanSpace ℂ I) (A : Matrix I I ℂ) :
    matrixStateCLM ψ A=(Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A ψ := rfl

omit [Nonempty I] in

/-- The norm of matrix evaluation at `ψ` is at most `‖ψ‖`. -/
theorem matrixStateCLM_norm (ψ : EuclideanSpace ℂ I) : ‖matrixStateCLM ψ‖≤‖ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  rw [matrixStateCLM_apply]
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,mul_comm] using
      ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) A).le_opNorm ψ

/-- The ordered product of the slots `exp(-i * θ j * G j) * W j` over `List.finRange K`. -/
def exponentialWord {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : Matrix I I ℂ :=
  paramWord (fun j => expSlot (G j) (W j) j) (List.finRange K) θ

/-- The continuous real-linear product-rule expression for the derivative of the exponential
word. -/
def exponentialWordD {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]Matrix I I ℂ :=
  paramWordD (fun j => expSlot (G j) (W j) j) (fun j => expSlotD (G j) (W j) j) (List.finRange K) θ

/-- The state obtained by applying the exponential circuit word to `ψ`. -/
def wordState {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℂ I :=
  matrixStateCLM ψ (exponentialWord G W θ)

/-- The exponential-word derivative composed with evaluation at the input state `ψ`. -/
def wordStateD {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]EuclideanSpace ℂ I :=
  (matrixStateCLM ψ).comp (exponentialWordD G W θ)

/-- The Euclidean operator represented by `O`, regarded as a real continuous linear map. -/
def observableCLM (O : Matrix I I ℂ) : EuclideanSpace ℂ I→L[ℝ]EuclideanSpace ℂ I :=
  ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) O).restrictScalars ℝ

/-- The real part of the observable expectation in the state produced by the exponential word. -/
def wordLoss {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  (inner ℂ (wordState G W ψ θ) ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) O (wordState G W ψ θ))).re

/-- The real continuous linear expression for the derivative of the exponential-word expectation
loss. -/
def wordLossD {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]ℝ :=
  expectationD (observableCLM O) (wordState G W ψ) (wordStateD G W ψ) θ

omit [Nonempty I] in

/-- The circuit loss equals the abstract quadratic expectation for `observableCLM O` and the
evolved state map. -/
theorem wordLoss_eq_expectation {K : ℕ} (G W : Fin K→Matrix I I ℂ) (O : Matrix I I ℂ)
    (ψ : EuclideanSpace ℂ I) : wordLoss G W O ψ=expectation (observableCLM O) (wordState G W ψ) := rfl

omit [Nonempty I] in

/-- The exponential word has Fréchet derivative `exponentialWordD` at every parameter vector. -/
theorem exponentialWord_hasFDerivAt {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (exponentialWord G W) (exponentialWordD G W θ) θ :=
  paramWord_hasFDerivAt _ _ (fun j x => expSlot_hasFDerivAt (G j) (W j) j x) _ θ

/-- An exponential word with Hermitian generators and fixed unitary gates has operator norm at
most one. -/
theorem exponentialWord_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖exponentialWord G W θ‖≤1 :=
  paramWord_norm _ (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le) _ θ

/-- With Hermitian generators of norm at most one and fixed unitary gates, the exponential-word
derivative has norm at most `K`. -/
theorem exponentialWordD_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ)
    (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖exponentialWordD G W θ‖≤K := by
  exact (paramWordD_norm _ _
    (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le)
    (fun j x => expSlotD_norm (G j) (W j) j (hG j) (hGn j) (hW j) x) _ θ).trans_eq (by simp)

/-- With Hermitian generators of norm at most one and fixed unitary gates, the exponential-word
derivative satisfies a global Lipschitz bound with constant `K²`. -/
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

/-- The evolved state map has Fréchet derivative `wordStateD` at every parameter vector. -/
theorem wordState_hasFDerivAt {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℝ (Fin K)) : HasFDerivAt (wordState G W ψ) (wordStateD G W ψ θ) θ :=
  (matrixStateCLM ψ).hasFDerivAt.comp θ (exponentialWord_hasFDerivAt G W θ)

/-- A unit input state evolved by Hermitian-generator slots and fixed unitary gates has norm at
most one. -/
theorem wordState_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖wordState G W ψ θ‖≤1 := by
  calc
    _ ≤ ‖matrixStateCLM ψ‖*‖exponentialWord G W θ‖ := (matrixStateCLM ψ).le_opNorm _
    _ ≤ 1*1 := mul_le_mul ((matrixStateCLM_norm ψ).trans_eq hψ)
      (exponentialWord_norm G W hG hW θ) (norm_nonneg _) zero_le_one
    _ = _ := one_mul 1

/-- For a unit input state, Hermitian generators of norm at most one, and fixed unitary gates,
the state derivative has norm at most `K`. -/
theorem wordStateD_norm {K : ℕ} (G W : Fin K→Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hψ : ‖ψ‖=1) (hG : ∀j,(G j).IsHermitian) (hGn : ∀j,‖G j‖≤1)
    (hW : ∀j,W j∈Matrix.unitaryGroup I ℂ) (θ : EuclideanSpace ℝ (Fin K)) :
    ‖wordStateD G W ψ θ‖≤K := by
  calc
    _ ≤ ‖matrixStateCLM ψ‖*‖exponentialWordD G W θ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*K := mul_le_mul ((matrixStateCLM_norm ψ).trans_eq hψ)
      (exponentialWordD_norm G W hG hGn hW θ) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- For a unit input state, Hermitian generators of norm at most one, and fixed unitary gates,
the state derivative satisfies a global Lipschitz bound with constant `K²`. -/
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
