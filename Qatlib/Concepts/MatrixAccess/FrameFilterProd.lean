/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.MatrixAccess.FrameFilterProd

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable def frameFlagFilter {H M : Type} [Fintype H] [DecidableEq H] [Fintype M]
    [DecidableEq M] (F : Matrix H M ℂ) : Matrix (Bool × H) (Bool × H) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) (rangeProjector F) +
    TensorGate PauliX (1 - rangeProjector F)

def flagFrame {H I : Type} (R : Matrix H I ℂ) : Matrix (Bool × H) I ℂ :=
  Matrix.of fun p i => if p.1 = false then R p.2 i else 0

noncomputable def frameFilteredProduct {H M : Type} [Fintype H] [DecidableEq H] [Fintype M]
    [DecidableEq M] (F : Matrix H M ℂ) (U V : Matrix H H ℂ) :
    Matrix (Bool × H) (Bool × H) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) V * frameFlagFilter F *
    TensorGate (1 : Matrix Bool Bool ℂ) U

@[simp] theorem flagFrame_apply {H I : Type} (R : Matrix H I ℂ) (p : Bool × H) (i : I) :
    flagFrame R p i = if p.1 = false then R p.2 i else 0 := rfl

theorem flagFrame_false {H I : Type} (R : Matrix H I ℂ) (h : H) (i : I) :
    flagFrame R (false, h) i = R h i := rfl

theorem flagFrame_true {H I : Type} (R : Matrix H I ℂ) (h : H) (i : I) :
    flagFrame R (true, h) i = 0 := rfl

theorem flagFrame_conjTranspose_apply {H I : Type} (R : Matrix H I ℂ) (i : I)
    (p : Bool × H) :
    (flagFrame R)ᴴ i p = if p.1 = false then (Rᴴ) i p.2 else 0 := by
  obtain ⟨b, h⟩ := p
  cases b <;> simp [Matrix.conjTranspose_apply]

private theorem tensorGate_zero_right {H J : Type} [Fintype H] [DecidableEq H] [Fintype J]
    [DecidableEq J] (U : Matrix H H ℂ) : TensorGate U (0 : Matrix J J ℂ) = 0 :=
  Matrix.kronecker_zero U

private theorem tensorGate_add_right {H J : Type} [Fintype H] [DecidableEq H] [Fintype J]
    [DecidableEq J] (U : Matrix H H ℂ) (A B : Matrix J J ℂ) :
    TensorGate U A + TensorGate U B = TensorGate U (A + B) :=
  (Matrix.kronecker_add U A B).symm

theorem frame_filter_actual_unitary_and_success_block (H M : Type) [Fintype H]
    [DecidableEq H] [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (hF : IsIsometry F) :
    frameFlagFilter F ∈ Matrix.unitaryGroup (Bool × H) ℂ ∧
      ∀ x y : H, frameFlagFilter F (false, x) (false, y) = rangeProjector F x y := by
  have hP : IsOrthogonalProjector (rangeProjector F) := rangeProjector_isOrthogonalProjector hF
  have hid : rangeProjector F * rangeProjector F = rangeProjector F := hP.1
  have hstar : (rangeProjector F)ᴴ = rangeProjector F := hP.2
  have hX2 : PauliX * PauliX = 1 := permMatrix_mul_self Bool.not_not
  have hXH : PauliXᴴ = PauliX := permMatrix_conjTranspose Bool.not_not
  have h01 : rangeProjector F * (1 - rangeProjector F) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hid, sub_self]
  have h10 : (1 - rangeProjector F) * rangeProjector F = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hid, sub_self]
  have h11 : (1 - rangeProjector F) * (1 - rangeProjector F) = 1 - rangeProjector F := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, h01, sub_zero]
  have hself : (frameFlagFilter F)ᴴ = frameFlagFilter F := by
    rw [frameFlagFilter, Matrix.conjTranspose_add, tensorGate_conjTranspose,
      tensorGate_conjTranspose, Matrix.conjTranspose_one, hstar, hXH,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
  have hsum : rangeProjector F + (1 - rangeProjector F) = 1 := by module
  have hsq : frameFlagFilter F * frameFlagFilter F = 1 := by
    rw [frameFlagFilter]
    simp only [Matrix.add_mul, Matrix.mul_add, tensorGate_mul]
    rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hX2, hid, h01, h10, h11,
      tensorGate_zero_right, add_zero, zero_add, tensorGate_add_right,
      hsum, tensorGate_one]
  exact ⟨by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hself, hsq],
    fun x y => by
      simp [frameFlagFilter, TensorGate, Matrix.one_apply, PauliX, permMatrix]⟩

section
variable {H I M O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

private theorem tensorGate_one_mul_flagFrame_apply (W : Matrix H H ℂ) (R : Matrix H I ℂ)
    (p : Bool × H) (i : I) :
    (TensorGate (1 : Matrix Bool Bool ℂ) W * flagFrame R) p i =
      if p.1 = false then (W * R) p.2 i else 0 := by
  obtain ⟨b, h⟩ := p
  cases b with
  | false =>
      have hval : (TensorGate (1 : Matrix Bool Bool ℂ) W * flagFrame R) (false, h) i
          = ∑ x : H, W h x * R x i := by
        simp [Matrix.mul_apply, TensorGate, Matrix.one_apply, flagFrame_apply,
          Fintype.sum_prod_type]
      rw [hval, if_pos rfl]
      rfl
  | true =>
      have hval : (TensorGate (1 : Matrix Bool Bool ℂ) W * flagFrame R) (true, h) i = 0 := by
        simp [Matrix.mul_apply, TensorGate, Matrix.one_apply, flagFrame_apply,
          Fintype.sum_prod_type]
      rw [hval, if_neg (by simp)]

private theorem tensorGate_pauliX_mul_flagFrame_apply (Y : Matrix H H ℂ) (R : Matrix H I ℂ)
    (p : Bool × H) (i : I) :
    (TensorGate PauliX Y * flagFrame R) p i =
      if p.1 = true then (Y * R) p.2 i else 0 := by
  obtain ⟨b, h⟩ := p
  cases b with
  | false =>
      have hval : (TensorGate PauliX Y * flagFrame R) (false, h) i = 0 := by
        simp [Matrix.mul_apply, TensorGate, PauliX, permMatrix, flagFrame_apply,
          Fintype.sum_prod_type]
      rw [hval, if_neg (by simp)]
  | true =>
      have hval : (TensorGate PauliX Y * flagFrame R) (true, h) i
          = ∑ x : H, Y h x * R x i := by
        simp [Matrix.mul_apply, TensorGate, PauliX, permMatrix, flagFrame_apply,
          Fintype.sum_prod_type]
      rw [hval, if_pos rfl]
      rfl

private theorem tensorGate_one_mul_flagFrame (W : Matrix H H ℂ) (R : Matrix H I ℂ) :
    TensorGate (1 : Matrix Bool Bool ℂ) W * flagFrame R = flagFrame (W * R) := by
  ext p i
  rw [tensorGate_one_mul_flagFrame_apply]
  obtain ⟨b, h⟩ := p
  cases b <;> simp

private theorem flagFrame_conjTranspose_mul_flagFrame (L : Matrix H O ℂ) (X : Matrix H I ℂ) :
    (flagFrame L)ᴴ * flagFrame X = Lᴴ * X := by
  ext o i
  have h1 : ∀ p : Bool × H, (flagFrame L)ᴴ o p * flagFrame X p i =
      if p.1 = false then (Lᴴ) o p.2 * X p.2 i else 0 := by
    intro p
    rw [flagFrame_conjTranspose_apply]
    obtain ⟨b, h⟩ := p
    cases b with
    | false => rw [if_pos rfl, if_pos rfl]; rfl
    | true => rw [if_neg (by simp), if_neg (by simp), zero_mul]
  show ∑ p : Bool × H, (flagFrame L)ᴴ o p * flagFrame X p i = (Lᴴ * X) o i
  rw [Finset.sum_congr rfl fun p _ => h1 p, Fintype.sum_prod_type, Fintype.sum_bool]
  simp
  rfl

private theorem flagFrame_conjTranspose_mul_pauliX_zero (L : Matrix H O ℂ) (Y : Matrix H H ℂ)
    (R : Matrix H I ℂ) :
    (flagFrame L)ᴴ * TensorGate PauliX Y * flagFrame R = 0 := by
  rw [Matrix.mul_assoc]
  ext o i
  have h1 : ∀ p : Bool × H, (flagFrame L)ᴴ o p * (TensorGate PauliX Y * flagFrame R) p i
      = 0 := by
    intro p
    rw [flagFrame_conjTranspose_apply, tensorGate_pauliX_mul_flagFrame_apply]
    obtain ⟨b, h⟩ := p
    cases b with
    | false => rw [if_pos rfl, if_neg (by simp), mul_zero]
    | true => rw [if_neg (by simp), zero_mul]
  show ∑ p : Bool × H,
      (flagFrame L)ᴴ o p * (TensorGate PauliX Y * flagFrame R) p i = (0 : Matrix O I ℂ) o i
  rw [Finset.sum_congr rfl fun p _ => h1 p]
  exact Finset.sum_const_zero

private theorem flagFrame_conjTranspose_mul_tensorGate (L : Matrix H O ℂ) (W : Matrix H H ℂ)
    (R : Matrix H I ℂ) :
    (flagFrame L)ᴴ * TensorGate (1 : Matrix Bool Bool ℂ) W * flagFrame R = Lᴴ * W * R := by
  rw [Matrix.mul_assoc, tensorGate_one_mul_flagFrame, flagFrame_conjTranspose_mul_flagFrame,
    Matrix.mul_assoc]

theorem flagFrame_isIsometry {R : Matrix H I ℂ} (hR : IsIsometry R) :
    IsIsometry (flagFrame R) := by
  show (flagFrame R)ᴴ * flagFrame R = 1
  rw [flagFrame_conjTranspose_mul_flagFrame, show Rᴴ * R = 1 from hR]

end

theorem frame_filtered_rectangular_corner_product (H I M O : Type) [Fintype H]
    [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M] [Fintype O]
    [DecidableEq O] (R : Matrix H I ℂ) (F : Matrix H M ℂ) (L : Matrix H O ℂ)
    (U V : Matrix H H ℂ) :
    compress (flagFrame L) (frameFilteredProduct F U V) (flagFrame R) =
      compress L V F * compress F U R := by
  have hW : frameFilteredProduct F U V =
      TensorGate (1 : Matrix Bool Bool ℂ) (V * rangeProjector F * U) +
        TensorGate PauliX (V * (1 - rangeProjector F) * U) := by
    rw [frameFilteredProduct, frameFlagFilter]
    simp only [Matrix.add_mul, Matrix.mul_add, tensorGate_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
  show (flagFrame L)ᴴ * frameFilteredProduct F U V * flagFrame R =
    compress L V F * compress F U R
  rw [hW, Matrix.mul_add, Matrix.add_mul, flagFrame_conjTranspose_mul_tensorGate,
    flagFrame_conjTranspose_mul_pauliX_zero, add_zero]
  show Lᴴ * (V * rangeProjector F * U) * R = Lᴴ * V * F * (Fᴴ * U * R)
  simp only [rangeProjector, ← Matrix.mul_assoc]

theorem frame_filtered_scaled_approximate_product (H I M O : Type) [Fintype H]
    [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M] [Fintype O]
    [DecidableEq O] (A : Matrix M I ℂ) (B : Matrix O M ℂ) (R : Matrix H I ℂ)
    (F : Matrix H M ℂ) (L : Matrix H O ℂ) (U V : Matrix H H ℂ) (α β ε η : ℝ)
    (h1 : BlockEncoding A U F R α ε) (h2 : BlockEncoding B V L F β η) :
    BlockEncoding (B * A) (frameFilteredProduct F U V) (flagFrame L) (flagFrame R)
      (α * β) (β * ε + α * η + ε * η) := by
  have hcU : ‖compress F U R‖ ≤ 1 :=
    l2_norm_compress_le_one h1.left_isometry h1.unitary h1.right_isometry
  have hcV : ‖compress L V F‖ ≤ 1 :=
    l2_norm_compress_le_one h2.left_isometry h2.unitary h2.right_isometry
  have hAnorm : ‖A‖ ≤ ε + α := by
    calc ‖A‖ = ‖(A - α • compress F U R) + α • compress F U R‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - α • compress F U R‖ + ‖α • compress F U R‖ := norm_add_le _ _
      _ ≤ ε + α := by
          refine add_le_add h1.error_le ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos h1.normalization_pos]
          exact (mul_le_mul_of_nonneg_left hcU (le_of_lt h1.normalization_pos)).trans_eq
            (mul_one α)
  have hexpr : (α * β) • compress (flagFrame L) (frameFilteredProduct F U V) (flagFrame R) =
      (β • compress L V F) * (α • compress F U R) := by
    rw [frame_filtered_rectangular_corner_product H I M O R F L U V]
    ext o i
    simp only [Matrix.smul_apply, Matrix.mul_apply, Complex.real_smul, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  refine ⟨(Matrix.unitaryGroup (Bool × H) ℂ).mul_mem
      ((Matrix.unitaryGroup (Bool × H) ℂ).mul_mem
        (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem h2.unitary)
        ((frame_filter_actual_unitary_and_success_block H M F h1.left_isometry).1))
      (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem h1.unitary),
    flagFrame_isIsometry h2.left_isometry, flagFrame_isIsometry h1.right_isometry,
    mul_pos h1.normalization_pos h2.normalization_pos,
    add_nonneg (add_nonneg (mul_nonneg (le_of_lt h2.normalization_pos) h1.error_nonneg)
        (mul_nonneg (le_of_lt h1.normalization_pos) h2.error_nonneg))
      (mul_nonneg h1.error_nonneg h2.error_nonneg), ?_⟩
  calc ‖B * A - (α * β) • compress (flagFrame L) (frameFilteredProduct F U V)
        (flagFrame R)‖
      = ‖B * A - (β • compress L V F) * (α • compress F U R)‖ := by rw [hexpr]
    _ ≤ ‖B - β • compress L V F‖ * ‖A‖ +
        ‖β • compress L V F‖ * ‖A - α • compress F U R‖ :=
        l2_norm_rect_mul_sub_mul_le B (β • compress L V F) A (α • compress F U R)
    _ ≤ η * (ε + α) + β * ε := by
        refine add_le_add (mul_le_mul h2.error_le hAnorm (norm_nonneg A) h2.error_nonneg) ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h2.normalization_pos]
        exact mul_le_mul
          ((mul_le_mul_of_nonneg_left hcV (le_of_lt h2.normalization_pos)).trans_eq
            (mul_one β))
          h1.error_le (norm_nonneg _) (le_of_lt h2.normalization_pos)
    _ = β * ε + α * η + ε * η := by ring

theorem frame_filtered_actual_conditional_output (H I M O : Type) [Fintype H]
    [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M] [Fintype O]
    [DecidableEq O] (A : Matrix M I ℂ) (B : Matrix O M ℂ) (R : Matrix H I ℂ)
    (F : Matrix H M ℂ) (L : Matrix H O ℂ) (U V : Matrix H H ℂ) (α β ε η : ℝ)
    (b : QState I) (h1 : BlockEncoding A U F R α ε) (h2 : BlockEncoding B V L F β η)
    (hb : Normalized b) :
    let x := (B * A) *ᵥ b
    let y := compress (flagFrame L) (frameFilteredProduct F U V) (flagFrame R) *ᵥ b
    let e := β * ε + α * η + ε * η
    e < ‖stateVector x‖ →
      y ≠ 0 ∧ ((‖stateVector x‖ - e) / (α * β)) ^ 2 ≤ MeasureProb y Finset.univ ∧
        ‖stateVector (PostMeasure y Finset.univ) - NormedSpace.normalize (stateVector x)‖ ≤
          2 * e / ‖stateVector x‖ := by
  intro x y e hgap
  have hBE := frame_filtered_scaled_approximate_product H I M O A B R F L U V α β ε η h1 h2
  have herr : ‖stateVector x - (α * β) • stateVector y‖ ≤ e :=
    (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error hBE) hb
  have hclose : ‖(α * β) • stateVector y - stateVector x‖ ≤ e := by
    rw [norm_sub_rev]
    exact herr
  obtain ⟨hy0, hout⟩ := normalize_error_of_gap hclose hgap
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    refine hy0 ?_
    have hz : stateVector y = 0 := by rw [h0]; rfl
    rw [hz, smul_zero]
  · have hlower := (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hBE) hb (le_of_lt hgap)
    rwa [postselectionProbability_eq_norm_sq hBE.left_isometry, stateVector_norm_sq] at hlower
  · rw [stateVector_postMeasure_univ]
    rw [NormedSpace.normalize_smul_of_pos (mul_pos h1.normalization_pos
      h2.normalization_pos)] at hout
    exact hout

end Qatlib.Concepts.MatrixAccess.FrameFilterProd
