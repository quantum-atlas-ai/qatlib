/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapSharp
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

/-! A single-node original-oracle consumer for the gap-sensitive estimate. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The finite construction in `NativeNeumannGapResolvent` satisfies `gap_reference_shift_eq` under the displayed hypotheses. -/
private theorem gap_reference_shift_eq (A : Matrix I I ℂ) (B : ℝ) (z : ℂ) :
    referenceShiftBlock A B z = ((B⁻¹ : ℝ) : ℂ) • matrixShift A z := by
  simp only [referenceShiftBlock, matrixShift, smul_sub, smul_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

/-- The finite construction in `NativeNeumannGapResolvent` satisfies `gap_reference_shift_norm` under the displayed hypotheses. -/
private theorem gap_reference_shift_norm (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α B : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : α + ‖z‖ ≤ B) : ‖referenceShiftBlock A B z‖ ≤ 1 := by
  have hc := Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one hbe.left_isometry hbe.unitary hbe.right_isometry
  have hs : ‖α • compress F U F‖ ≤ α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbe.normalization_pos]
    exact (mul_le_mul_of_nonneg_left hc hbe.normalization_pos.le).trans_eq (mul_one α)
  have hA : ‖A‖ ≤ α := by
    calc
      ‖A‖ = ‖(A - α • compress F U F) + α • compress F U F‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - α • compress F U F‖ + ‖α • compress F U F‖ := norm_add_le _ _
      _ ≤ α := by linarith [hbe.error_le]
  have hz : ‖z • (1 : Matrix I I ℂ)‖ ≤ ‖z‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I)) (norm_nonneg z)).trans_eq
      (mul_one ‖z‖)
  have hshift : ‖matrixShift A z‖ ≤ B := by
    change ‖z • (1 : Matrix I I ℂ) - A‖ ≤ B
    calc
      _ ≤ ‖z • (1 : Matrix I I ℂ)‖ + ‖A‖ := norm_sub_le _ _
      _ ≤ B := by linarith
  rw [gap_reference_shift_eq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hB)]
  exact (mul_le_mul_of_nonneg_left hshift (inv_nonneg.mpr hB.le)).trans_eq
    (inv_mul_cancel₀ hB.ne')

/-- Gap-sensitive error for the actual original-oracle word.  The error
certificate is the native coefficient error itself, with an explicit smallness
condition.  This does not certify numerical parameter generation. -/
theorem native_original_neumann_resolvent_gap
    (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B r K : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : α + ‖z‖ ≤ B) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖)
    (hK : jointResolventCondition B r ≤ K)
    (hsmall : nativeCoefficientError ps p slack α B z ≤ 1/(4*K^2)) :
    WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock ps p slack A α) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))
        (nativeOriginalNeumannWord b hb F ps p slack))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)) ∧
    ‖((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock ps p slack A α) b -
      matrixResolvent A z‖ ≤
      ((2*K^2+4*K^3) * nativeCoefficientError ps p slack α B z +
        reciprocalError (jointResolventCondition B r)⁻¹ b) / B ∧
    adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
      2*b + (2*b-1)*(436+(if slack then 1 else 0)) := by
  let S := referenceShiftBlock A B z
  let X := nativeShiftBlock ps p slack A α
  let κ := jointResolventCondition B r
  have hS : ‖S‖ ≤ 1 := gap_reference_shift_norm A U F α B z hbe hB hbound
  have hw := native_original_neumann_resolvent b hb ps p slack A U F α B r z hbe hB hbound hr hsep
  have hinput := native_original_shift_coefficient_error ps p slack A U F α B z hbe
  have hX : ‖X‖ ≤ 1 := by
    change ‖identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
      (oracleCoefficient ps p slack / (α : ℂ)) • A‖ ≤ 1
    rw [← hinput.1.encoded]
    exact (compress_norm_le hinput.1.left_isometry hinput.1.right_isometry _).trans
      (unitary_norm_le_one hinput.1.unitary)
  have hd : ‖X-S‖ ≤ nativeCoefficientError ps p slack α B z := hinput.2
  have hκ2 : 2 ≤ κ := le_max_left _ _
  have hκ : 0 < κ := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hκ1 : κ⁻¹ ≤ 1 := (inv_le_one₀ hκ).mpr (by linarith)
  have hi : κ⁻¹ ≤ r / B := by
    have hh := (inv_le_inv₀ hκ (div_pos hB hr)).mpr (le_max_right 2 (B / r))
    simpa only [inv_div] using hh
  have hsing (i : Fin (Fintype.card I)) : κ⁻¹ ≤ matrixSingularValues S i := by
    apply hi.trans
    have hh := normalized_matrixShift_lower_bound A z B r hB hsep (rightSingularBasis S i)
    rw [← gap_reference_shift_eq] at hh
    change (r / B) * ‖rightSingularBasis S i‖ ≤ ‖S.toEuclideanLin (rightSingularBasis S i)‖ at hh
    simpa only [norm_rightSingularBasis, norm_apply_rightSingularBasis, mul_one] using hh
  have hgap (i : Fin (Fintype.card I)) : K⁻¹ ≤ matrixSingularValues S i :=
    ((inv_le_inv₀ hKp hκ).mpr hK).trans (hsing i)
  have hpoly : ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b - Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b‖ ≤
      (2*K^2+4*K^3)*nativeCoefficientError ps p slack α B z :=
    leftDefectNeumann_gap_perturbation_sharp X S K _ b hK1 hX hS hgap hd hsmall
  have hc : ((B⁻¹ : ℝ) : ℂ) * (B : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hB.ne', Complex.ofReal_one]
  have hforward : S * ((B : ℂ) • matrixResolvent A z) = 1 := by
    dsimp only [S]
    rw [gap_reference_shift_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A z r hr hsep).1, hc, one_smul]
  have hbackward : ((B : ℂ) • matrixResolvent A z) * S = 1 := by
    dsimp only [S]
    rw [gap_reference_shift_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A z r hr hsep).2, mul_comm (B : ℂ), hc, one_smul]
  have hpseudo : matrixPseudoinverse S = (B : ℂ) • matrixResolvent A z :=
    matrixPseudoinverse_eq_of_twoSidedInverse S _ hforward hbackward
  have htail := reciprocalMatrixApprox_error_le S (inv_pos.mpr hκ) hκ1
    (fun i => (matrixSingularValues_le_spectralNorm _ i).trans hS)
    (fun i _ => hsing i) b
  rw [← Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann_eq_reciprocalMatrixApprox, hpseudo] at htail
  have ht : ((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b - matrixResolvent A z =
      ((B⁻¹ : ℝ) : ℂ) • (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b - (B : ℂ) • matrixResolvent A z) := by
    rw [smul_sub, smul_smul, hc, one_smul]
  have htail' : ‖((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b - matrixResolvent A z‖ ≤
      reciprocalError κ⁻¹ b / B := by
    rw [ht, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hB)]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hB.le)
  have herr : ‖((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b - matrixResolvent A z‖ ≤
      ((2*K^2+4*K^3)*nativeCoefficientError ps p slack α B z + reciprocalError κ⁻¹ b) / B := by
    have hdecomp : ((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b - matrixResolvent A z =
        ((B⁻¹ : ℝ) : ℂ) • (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b - Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b) +
          (((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b - matrixResolvent A z) := by
      rw [smul_sub]
      abel
    rw [hdecomp]
    calc
      _ ≤ ‖((B⁻¹ : ℝ) : ℂ) • (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b - Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b)‖ +
          ‖((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b - matrixResolvent A z‖ := norm_add_le _ _
      _ ≤ B⁻¹ * ((2*K^2+4*K^3)*nativeCoefficientError ps p slack α B z) +
          reciprocalError κ⁻¹ b / B := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
        exact add_le_add (mul_le_mul_of_nonneg_left hpoly (inv_nonneg.mpr hB.le)) htail'
      _ = _ := by rw [add_div]; ring
  exact ⟨hw.1, hw.2.1, herr, hw.2.2.2⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
