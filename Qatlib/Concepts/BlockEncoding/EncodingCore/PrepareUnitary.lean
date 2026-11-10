/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.CoefficientLCU
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.LCU
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

local notation:70 A " ⬝ₘ " B =>
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

variable {J I : Type*} [Fintype J] [DecidableEq J]

noncomputable def preparationDenominator (r : J → ℝ) (j₀ : J) : ℝ :=
  Real.sqrt (2 * (1 + r j₀))

noncomputable def preparationAxis (r : J → ℝ) (j₀ : J) (j : J) : ℂ :=
  ((((if j = j₀ then 1 else 0) + r j) / preparationDenominator r j₀ : ℝ) : ℂ)

noncomputable def nonnegativePrepare (r : J → ℝ) (j₀ : J) : Matrix J J ℂ :=
  Qatlib.Foundations.PureStateMath.Reflection.ReflectionAbout
    (rangeProjector (Matrix.replicateCol (Fin 1) (preparationAxis r j₀)))

omit [Fintype J] [DecidableEq J] in

theorem preparationDenominator_pos (r : J → ℝ) (j₀ : J) (hr : ∀ j, 0 ≤ r j) :
    0 < preparationDenominator r j₀ := by
  apply Real.sqrt_pos.mpr
  linarith [hr j₀]

omit [Fintype J] [DecidableEq J] in

theorem preparationDenominator_sq (r : J → ℝ) (j₀ : J) (hr : ∀ j, 0 ≤ r j) :
    preparationDenominator r j₀ ^ 2 = 2 * (1 + r j₀) := by
  exact Real.sq_sqrt (by linarith [hr j₀])

private theorem preparationVector_sum_sq (r : J → ℝ) (j₀ : J)
    (hn : ∑ j, (r j)^2 = 1) :
    ∑ j, ((if j = j₀ then 1 else 0) + r j)^2 = 2 * (1 + r j₀) := by
  classical
  calc
    _ = ∑ j, ((r j)^2 + if j = j₀ then 1 + 2 * r j₀ else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = j₀
      · subst j
        simp only [ite_true]
        ring
      · simp [hj]
    _ = _ := by rw [Finset.sum_add_distrib, hn]; simp; ring

theorem preparationAxis_normalized (r : J → ℝ) (j₀ : J)
    (hr : ∀ j, 0 ≤ r j) (hn : ∑ j, (r j)^2 = 1) :
    ∑ j, star (preparationAxis r j₀ j) * preparationAxis r j₀ j = 1 := by
  have hs : ∑ j, (((if j = j₀ then 1 else 0) + r j) /
      preparationDenominator r j₀)^2 = 1 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, preparationVector_sum_sq r j₀ hn,
      preparationDenominator_sq r j₀ hr]
    exact div_self (by linarith [hr j₀])
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hs
  simpa [preparationAxis, Complex.star_def, pow_two] using hc

omit [DecidableEq J] in

theorem replicateCol_isIsometry (a : J → ℂ)
    (ha : ∑ j, star (a j) * a j = 1) :
    IsIsometry (Matrix.replicateCol (Fin 1) a) := by
  unfold IsIsometry
  ext i k
  have hik : i = k := Subsingleton.elim _ _
  subst k
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using ha

theorem nonnegativePrepare_unitary (r : J → ℝ) (j₀ : J)
    (hr : ∀ j, 0 ≤ r j) (hn : ∑ j, (r j)^2 = 1) :
    nonnegativePrepare r j₀ ∈ Matrix.unitaryGroup J ℂ := by
  apply Qatlib.Foundations.PureStateMath.Reflection.reflectionAbout_unitary
  apply rangeProjector_isOrthogonalProjector
  exact replicateCol_isIsometry _ (preparationAxis_normalized r j₀ hr hn)

omit [Fintype J] in

theorem nonnegativePrepare_column (r : J → ℝ) (j₀ : J)
    (hr : ∀ j, 0 ≤ r j) (j : J) :
    nonnegativePrepare r j₀ j j₀ = (r j : ℂ) := by
  have hd2 := preparationDenominator_sq r j₀ hr
  have hratio : 2 * (1 + r j₀) /
      (preparationDenominator r j₀ * preparationDenominator r j₀) = 1 := by
    rw [← pow_two, hd2]
    exact div_self (by linarith [hr j₀])
  have he : 2 * (((if j = j₀ then 1 else 0) + r j) / preparationDenominator r j₀) *
      ((1 + r j₀) / preparationDenominator r j₀) -
      (if j = j₀ then 1 else 0) = r j := by
    calc
      _ = ((if j = j₀ then 1 else 0) + r j) *
          (2 * (1 + r j₀) /
            (preparationDenominator r j₀ * preparationDenominator r j₀)) -
          (if j = j₀ then 1 else 0) := by ring
      _ = _ := by rw [hratio]; ring
  have hc := congrArg (fun x : ℝ => (x : ℂ)) he
  by_cases hj : j = j₀ <;>
    simpa [nonnegativePrepare, Qatlib.Foundations.PureStateMath.Reflection.ReflectionAbout, rangeProjector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      preparationAxis, Complex.star_def, hj, mul_assoc] using hc

theorem nonnegativePrepare_mulVec_ket (r : J → ℝ) (j₀ : J)
    (hr : ∀ j, 0 ≤ r j) :
    nonnegativePrepare r j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = fun j => (r j : ℂ) := by
  ext j
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using
    nonnegativePrepare_column r j₀ hr j

noncomputable def complexPrepare (v : J → ℂ) (zero : J) : Matrix J J ℂ :=
  Matrix.diagonal (fun j => coefficientPhase (v j)) *
    nonnegativePrepare (fun j => ‖v j‖) zero

theorem complexPrepare_unitary (v : J → ℂ) (zero : J)
    (hv : Qatlib.Foundations.PureStateMath.Normalized v) :
    complexPrepare v zero ∈ Matrix.unitaryGroup J ℂ := by
  have hd : Matrix.diagonal (fun j => coefficientPhase (v j)) ∈
      Matrix.unitaryGroup J ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact coefficientPhase_unit (v j)
  exact (Matrix.unitaryGroup J ℂ).mul_mem hd
    (nonnegativePrepare_unitary _ zero (fun j => norm_nonneg (v j)) hv)

theorem complexPrepare_mulVec_ket (v : J → ℂ) (zero : J) :
    complexPrepare v zero *ᵥ Qatlib.Foundations.PureStateMath.Ket zero = v := by
  rw [complexPrepare, ← Matrix.mulVec_mulVec,
    nonnegativePrepare_mulVec_ket _ zero (fun j => norm_nonneg (v j))]
  ext j
  simpa only [Matrix.mulVec_diagonal, mul_comm] using norm_mul_coefficientPhase (v j)

section Coefficients

noncomputable def coefficientPrepare (c : J → ℂ) (j₀ : J) : Matrix J J ℂ :=
  nonnegativePrepare (fun j => Real.sqrt (‖c j‖ / coefficientMass c)) j₀

omit [DecidableEq J] in

private theorem coefficientSqrt_sum_sq (c : J → ℂ) (hα : 0 < coefficientMass c) :
    ∑ j, (Real.sqrt (‖c j‖ / coefficientMass c))^2 = 1 := by
  simp_rw [Real.sq_sqrt (div_nonneg (norm_nonneg _) hα.le)]
  rw [← Finset.sum_div]
  exact div_self hα.ne'

theorem coefficientPrepare_unitary (c : J → ℂ) (j₀ : J)
    (hα : 0 < coefficientMass c) :
    coefficientPrepare c j₀ ∈ Matrix.unitaryGroup J ℂ :=
  nonnegativePrepare_unitary _ _ (fun _ => Real.sqrt_nonneg _)
    (coefficientSqrt_sum_sq c hα)

theorem coefficientPrepare_mulVec_ket (c : J → ℂ) (j₀ : J) :
    coefficientPrepare c j₀ *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = coefficientAmplitude c :=
  nonnegativePrepare_mulVec_ket _ _ (fun _ => Real.sqrt_nonneg _)

end Coefficients

section Register

variable [Fintype I] [DecidableEq I]

noncomputable def prepareRegister (W : Matrix J J ℂ) : Matrix (J × I) (J × I) ℂ :=
  W ⊗ₖ (1 : Matrix I I ℂ)

theorem prepareRegister_unitary {W : Matrix J J ℂ}
    (hW : W ∈ Matrix.unitaryGroup J ℂ) :
    prepareRegister (I := I) W ∈ Matrix.unitaryGroup (J × I) ℂ :=
  Matrix.kronecker_mem_unitary hW (Matrix.unitaryGroup I ℂ).one_mem

omit [DecidableEq J] in

theorem prepareRegister_mul_prepareLift (W : Matrix J J ℂ) (a : J → ℂ) :
    (prepareRegister (I := I) W ⬝ₘ prepareLift a : Matrix (J × I) I ℂ) =
      prepareLift (W *ᵥ a) := by
  classical
  ext p i
  rcases p with ⟨j, k⟩
  by_cases hk : k = i
  · subst i
    simp [prepareRegister, prepareLift, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Matrix.mulVec, dotProduct, mul_ite]
  · simp [prepareRegister, prepareLift, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Matrix.mulVec, dotProduct, mul_ite, hk]

theorem coefficientPrepare_register_action (c : J → ℂ) (j₀ : J) :
    (prepareRegister (I := I) (coefficientPrepare c j₀) ⬝ₘ
        prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀) : Matrix (J × I) I ℂ) =
      prepareLift (coefficientAmplitude c) := by
  rw [prepareRegister_mul_prepareLift, coefficientPrepare_mulVec_ket]

noncomputable def coefficientLCUUnitary (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j₀ : J) : Matrix (J × I) (J × I) ℂ :=
  (prepareRegister (coefficientPrepare c j₀))ᴴ * select (phaseAbsorbed c U) *
    prepareRegister (coefficientPrepare c j₀)

theorem coefficientLCUUnitary_unitary (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j₀ : J) (hα : 0 < coefficientMass c)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    coefficientLCUUnitary c U j₀ ∈ Matrix.unitaryGroup (J × I) ℂ := by
  have hG := prepareRegister_unitary (I := I) (coefficientPrepare_unitary c j₀ hα)
  exact (Matrix.unitaryGroup (J × I) ℂ).mul_mem
    ((Matrix.unitaryGroup (J × I) ℂ).mul_mem (adjoint_unitary hG)
      (select_unitary _ (phaseAbsorbed_unitary c U hU))) hG

theorem coefficientLCUUnitary_compress (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j₀ : J) (hα : 0 < coefficientMass c) :
    compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) (coefficientLCUUnitary c U j₀)
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) =
        ∑ j, (c j / (coefficientMass c : ℂ)) • U j := by
  have he : compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) (coefficientLCUUnitary c U j₀)
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) =
    compress
      (prepareRegister (coefficientPrepare c j₀) ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀))
      (select (phaseAbsorbed c U))
      (prepareRegister (coefficientPrepare c j₀) ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
    simp [compress, coefficientLCUUnitary, Matrix.mul_assoc]
  rw [he, coefficientPrepare_register_action, prepare_select_compress,
    coefficientLCU_matrix c U hα]

theorem coefficientLCUUnitary_projectedEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j₀ : J) (hα : 0 < coefficientMass c)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, (c j / (coefficientMass c : ℂ)) • U j)
      (coefficientLCUUnitary c U j₀) (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀))
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
  have hE : IsIsometry (prepareLift (I := I) (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
    apply prepareLift_isIsometry
    simp [Qatlib.Foundations.PureStateMath.Ket]
  exact ⟨coefficientLCUUnitary_unitary c U j₀ hα hU, hE, hE,
    coefficientLCUUnitary_compress c U j₀ hα⟩

theorem coefficientLCUUnitary_blockEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j₀ : J) (hα : 0 < coefficientMass c)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    BlockEncoding (∑ j, c j • U j) (coefficientLCUUnitary c U j₀)
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀))
      (coefficientMass c) 0 := by
  have h := coefficientLCUUnitary_projectedEncoding c U j₀ hα hU
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, hα, le_rfl, ?_⟩
  rw [h.encoded, coefficientLCU_rescale c U hα, sub_self, norm_zero]

end Register

end Qatlib.Concepts.BlockEncoding.EncodingCore
