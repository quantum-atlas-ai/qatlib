/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000
local notation:70 A " ⬝ₘ " B => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B
variable {J K I H : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

noncomputable def pairedFrame (j0 : J) (k0 : K) : Matrix (J × (K × I)) I ℂ :=
  prepareLift (I := K × I) (Qatlib.Foundations.PureStateMath.Ket j0) * encodingFiber k0
noncomputable def pairedBody (PL PR : Matrix J J ℂ)
    (U : J → Matrix (K × I) (K × I) ℂ) : Matrix (J × (K × I)) (J × (K × I)) ℂ :=
  TensorGate PLᴴ (1 : Matrix (K × I) (K × I) ℂ) * select U *
    TensorGate PR (1 : Matrix (K × I) (K × I) ℂ)
noncomputable def pairedCircuit (PL PR : Matrix J J ℂ)
    (U : J → Matrix (K × I) (K × I) ℂ) : Circuit (J × (K × I)) :=
  [Step.gate (TensorGate PR (1 : Matrix (K × I) (K × I) ℂ)), Step.gate (select U),
   Step.gate (TensorGate PLᴴ (1 : Matrix (K × I) (K × I) ℂ))]

theorem paired_gram_actual_encoding : ∀ (F : Matrix H I ℂ) (UL UR : Matrix H H ℂ),
    IsIsometry F → UL ∈ Matrix.unitaryGroup H ℂ → UR ∈ Matrix.unitaryGroup H ℂ →
    ProjectedUnitaryEncoding
      (Matrix.of (fun i j => Qatlib.Foundations.PureStateMath.Inner (UL *ᵥ (F *ᵥ Qatlib.Foundations.PureStateMath.Ket i)) (UR *ᵥ (F *ᵥ Qatlib.Foundations.PureStateMath.Ket j))))
      (ULᴴ*UR) F F ∧
    (∀ psi : QState H, Run 1 [Step.gate UR,Step.gate ULᴴ] psi = ApplyGate (ULᴴ*UR) psi) ∧
    GateCount [Step.gate UR,Step.gate ULᴴ] = 2 := by
  intro F UL UR hF hUL hUR
  refine ⟨⟨(Matrix.unitaryGroup H ℂ).mul_mem (adjoint_unitary hUL) hUR,hF,hF,?_⟩,?_,by simp [GateCount]⟩
  · ext i j
    simp only [Matrix.of_apply, Qatlib.Foundations.PureStateMath.Inner, compress,
        Matrix.star_mulVec]
    rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Qatlib.Foundations.PureStateMath.Ket, dotProduct, Matrix.mulVec, Matrix.mul_assoc]
  · intro psi
    simp only [run_gate, run_nil, ApplyGate, Matrix.mulVec_mulVec]

theorem paired_prepare_columns_l1_bound : ∀ (PL PR : Matrix J J ℂ) (j0 : J),
    PL ∈ Matrix.unitaryGroup J ℂ → PR ∈ Matrix.unitaryGroup J ℂ →
    (∑ j, star (PL j j0)*PL j j0 = 1) ∧
    (∑ j, star (PR j j0)*PR j j0 = 1) ∧
    (∑ j, ‖star (PL j j0)*PR j j0‖) ≤ 1 := by
  intro PL PR j0 hPL hPR
  have hcol (P : Matrix J J ℂ) (hP : P ∈ Matrix.unitaryGroup J ℂ) :
      (∑ j, star (P j j0)*P j j0 = 1) := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hP
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun h j0) j0
  have hsq (P : Matrix J J ℂ) (hP : P ∈ Matrix.unitaryGroup J ℂ) : ∑ j, ‖P j j0‖^2 = 1 := by
    simpa [Normalized, ApplyGate, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct] using
      normalized_applyGate hP (normalized_ket j0)
  refine ⟨hcol PL hPL,hcol PR hPR,?_⟩
  simp only [norm_mul, norm_star]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => ‖PL j j0‖) (fun j => ‖PR j j0‖)
  rw [hsq PL hPL,hsq PR hPR] at h
  nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (norm_nonneg (PL j j0)) (norm_nonneg (PR j j0)))]

theorem pairedFrame_eq_tagFrame (j0 : J) (k0 : K) :
    pairedFrame (I := I) j0 k0 = tagFrame j0 (encodingFiber k0) := by
  exact (tagFrame_eq j0 (encodingFiber k0)).symm

theorem pairedFrame_isometry (j0 : J) (k0 : K) : IsIsometry (pairedFrame (I := I) j0 k0) := by
  rw [pairedFrame_eq_tagFrame]
  exact tagFrame_isIsometry j0 _ (encodingFiber_isIsometry k0)

theorem paired_column_action (P : Matrix J J ℂ) (j0 : J) :
    (TensorGate P (1 : Matrix (K×I) (K×I) ℂ) ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) =
      prepareLift (fun j => P j j0) := by
  have hket : P *ᵥ Qatlib.Foundations.PureStateMath.Ket j0 = (fun j => P j j0) := by
    ext j
    simp [Matrix.mulVec,Qatlib.Foundations.PureStateMath.Ket,dotProduct]
  have h :=
      prepareRegister_mul_prepareLift (I := K×I) P (Qatlib.Foundations.PureStateMath.Ket j0)
  rw [hket] at h
  exact h

theorem pairedBody_corner (PL PR : Matrix J J ℂ) (U : J → Matrix (K×I) (K×I) ℂ) (j0 : J) :
    compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) (pairedBody PL PR U) (prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) =
      lcuBilinearMatrix (fun j => PL j j0) (fun j => PR j j0) U := by
  have he : compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) (pairedBody PL PR U) (prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) =
      compress (TensorGate PL 1 ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) (select U)
        (TensorGate PR 1 ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j0)) := by
    simp [compress, pairedBody, tensorGate_conjTranspose, Matrix.mul_assoc]
  rw [he,paired_column_action,paired_column_action,prepare_select_compress_bilinear]

theorem pairedBody_unitary (PL PR : Matrix J J ℂ) (U : J → Matrix (K×I) (K×I) ℂ)
    (hPL : PL ∈ Matrix.unitaryGroup J ℂ) (hPR : PR ∈ Matrix.unitaryGroup J ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (K×I) ℂ) :
    pairedBody PL PR U ∈ Matrix.unitaryGroup (J×(K×I)) ℂ := by
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem (tensorGate_unitary (adjoint_unitary hPL) (by simp))
      (select_unitary U hU)) (tensorGate_unitary hPR (by simp))

theorem paired_prepare_actual_corner_and_word : ∀ (PL PR : Matrix J J ℂ)
    (U : J → Matrix (K×I) (K×I) ℂ) (j0 : J) (k0 : K),
    PL ∈ Matrix.unitaryGroup J ℂ → PR ∈ Matrix.unitaryGroup J ℂ →
    (∀ j, U j ∈ Matrix.unitaryGroup (K×I) ℂ) →
    IsIsometry (pairedFrame (I := I) j0 k0) ∧
    compress (pairedFrame j0 k0) (pairedBody PL PR U) (pairedFrame j0 k0) =
      ∑ j, (star (PL j j0)*PR j j0) • compress (encodingFiber k0) (U j) (encodingFiber k0) ∧
    IsUnitaryCircuit (pairedCircuit PL PR U) ∧ QueryCount (pairedCircuit PL PR U)=0 ∧
    GateCount (pairedCircuit PL PR U)=3 ∧
    (∀ psi : QState (J×(K×I)), Run 1 (pairedCircuit PL PR U) psi = ApplyGate (pairedBody PL PR U) psi) := by
  intro PL PR U j0 k0 hPL hPR hU
  refine ⟨pairedFrame_isometry j0 k0,?_,?_,by simp [pairedCircuit],by simp [pairedCircuit],?_⟩
  · rw [pairedFrame_eq_tagFrame, compress_tagFrame, pairedBody_corner, lcuBilinearMatrix,
      Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  · intro V hV
    simp only [pairedCircuit,List.mem_cons,List.not_mem_nil,or_false,Step.gate.injEq] at hV
    rcases hV with rfl|rfl|rfl
    · exact tensorGate_unitary hPR (by simp)
    · exact select_unitary U hU
    · exact tensorGate_unitary (adjoint_unitary hPL) (by simp)
  · intro psi
    simp [pairedCircuit,pairedBody,ApplyGate,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem paired_prepare_absolute_error_corrected : ∀ (PL PR : Matrix J J ℂ)
    (U : J → Matrix (K×I) (K×I) ℂ) (A : J → Matrix I I ℂ) (y : J → ℂ)
    (j0 : J) (k0 : K) (alpha beta eps1 eps2 : ℝ),
    PL ∈ Matrix.unitaryGroup J ℂ → PR ∈ Matrix.unitaryGroup J ℂ →
    0 < alpha → 0 < beta → 0 ≤ eps1 → (∑ j, ‖y j‖) ≤ beta →
    (∑ j, ‖(beta : ℂ)*(star (PL j j0)*PR j j0)-y j‖) ≤ eps1 →
    (∀ j, BlockEncoding (A j) (U j) (encodingFiber k0) (encodingFiber k0) alpha eps2) →
    BlockEncoding (∑ j, y j • A j) (pairedBody PL PR U)
      (pairedFrame j0 k0) (pairedFrame j0 k0) (alpha*beta) (alpha*eps1+beta*eps2) := by
  intro PL PR U A y j0 k0 alpha beta eps1 eps2 hPL hPR ha hb he1 hy herr henc
  let c : J → ℂ := fun j => star (PL j j0)*PR j j0
  let C : J → Matrix I I ℂ := fun j => compress (encodingFiber k0) (U j) (encodingFiber k0)
  have he2 : 0 ≤ eps2 := (henc j0).error_nonneg
  have hC (j : J) : ‖C j‖ ≤ 1 := l2_norm_compress_le_one
    (henc j).left_isometry (henc j).unitary (henc j).right_isometry
  have hcorner := (paired_prepare_actual_corner_and_word PL PR U j0 k0 hPL hPR
    (fun j => (henc j).unitary)).2.1
  have hsplit : (∑ j, y j • A j)-(alpha*beta) • (∑ j, c j • C j) =
      (∑ j, y j • (A j-alpha • C j))+alpha • (∑ j, (y j-(beta : ℂ)*c j) • C j) := by
    calc
      _ = ∑ j, (y j • A j-(alpha*beta) • (c j • C j)) := by
        rw [Finset.smul_sum,Finset.sum_sub_distrib]
      _ = ∑ j, (y j • (A j-alpha • C j)+alpha • ((y j-(beta : ℂ)*c j) • C j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ext a b
        simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
          Complex.real_smul,Complex.ofReal_mul]
        ring
      _ = _ := by rw [Finset.sum_add_distrib,Finset.smul_sum]
  have hterm : ‖∑ j, y j • (A j-alpha • C j)‖ ≤ beta*eps2 := by
    calc
      _ ≤ ∑ j, ‖y j • (A j-alpha • C j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖y j‖*eps2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (henc j).error_le (norm_nonneg _)
      _ = (∑ j, ‖y j‖)*eps2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hy he2
  have hcoeff : ‖∑ j, (y j-(beta : ℂ)*c j) • C j‖ ≤ eps1 := by
    calc
      _ ≤ ∑ j, ‖(y j-(beta : ℂ)*c j) • C j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖y j-(beta : ℂ)*c j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (hC j) (norm_nonneg _)).trans_eq (mul_one _)
      _ = ∑ j, ‖(beta : ℂ)*c j-y j‖ := by simp only [norm_sub_rev]
      _ ≤ _ := herr
  refine ⟨pairedBody_unitary PL PR U hPL hPR (fun j => (henc j).unitary),
    pairedFrame_isometry j0 k0,pairedFrame_isometry j0 k0,mul_pos ha hb,
    add_nonneg (mul_nonneg ha.le he1) (mul_nonneg hb.le he2),?_⟩
  rw [hcorner]
  change ‖(∑ j, y j • A j)-(alpha*beta) • (∑ j, c j • C j)‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖∑ j, y j • (A j-alpha • C j)‖+‖alpha • (∑ j, (y j-(beta : ℂ)*c j) • C j)‖ := norm_add_le _ _
    _ ≤ beta*eps2+alpha*eps1 := add_le_add hterm (by
      rw [norm_smul,Real.norm_of_nonneg ha.le]
      exact mul_le_mul_of_nonneg_left hcoeff ha.le)
    _ = _ := by ring

end Qatlib.Concepts.BlockEncoding.EncodingCore
