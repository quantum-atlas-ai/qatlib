/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeApproxInput
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
/-! The same original controlled-oracle word approximates the resolvent of
true A, with input error added before the same Neumann polynomial. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped Matrix.Norms.L2Operator
variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
/-- The finite construction in `NativeApproxResolvent` satisfies `native_approx_input_neumann_resolvent` under the displayed hypotheses. -/
theorem native_approx_input_neumann_resolvent
    (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B r e : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α e) (hB : 0 < B)
    (hbound : α + e + ‖z‖ ≤ B) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) :
    WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • leftDefectNeumann (nativeShiftBlock ps p slack (encodedInput U F α) α) b)
      (evaluate (uniformNeumannOracle b (nativeDataQuery U))
        (nativeOriginalNeumannWord b hb F ps p slack))
      (uniformNeumannFrame b hb (nativeDataFrame F))
      (uniformNeumannFrame b hb (nativeDataFrame F)) ∧
    ‖((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann (nativeShiftBlock ps p slack (encodedInput U F α) α) b -
      matrixResolvent A z‖ ≤
      ((b : ℝ)^2 * (nativeCoefficientError ps p slack α B z+e/B) +
        reciprocalError (jointResolventCondition B r)⁻¹ b) / B ∧
    adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
      2*b + (2*b-1)*(436+(if slack then 1 else 0)) := by
  let S := referenceShiftBlock A B z
  let X := nativeShiftBlock ps p slack (encodedInput U F α) α
  let κ := jointResolventCondition B r
  have hS : ‖S‖ ≤ 1 := approximate_reference_contraction A U F α B e z hbe hB hbound
  have hself := encodedInput_exact A U F α e hbe
  have hw := native_original_neumann_encoding b hb ps p slack (encodedInput U F α) U F α hself
  have hinput := native_approx_input_shift_error ps p slack A U F α B e z hbe hB
  have hX : ‖X‖ ≤ 1 := by
    change ‖nativeShiftBlock ps p slack (encodedInput U F α) α‖≤1
    rw [← hinput.1.encoded]
    exact (Qatlib.Concepts.BlockEncoding.Encoding.compress_norm_le hinput.1.left_isometry hinput.1.right_isometry _).trans
      (Qatlib.Concepts.BlockEncoding.Encoding.unitary_norm_le_one hinput.1.unitary)
  have hd : ‖X-S‖ ≤ (nativeCoefficientError ps p slack α B z+e/B) := hinput.2
  have hpoly : ‖leftDefectNeumann X b - leftDefectNeumann S b‖ ≤
      (b : ℝ)^2 * (nativeCoefficientError ps p slack α B z+e/B) :=
    (leftDefectNeumann_perturbation X S b hX hS).trans
      (mul_le_mul_of_nonneg_left hd (sq_nonneg (b : ℝ)))
  have reference_shift_eq (A : Matrix I I ℂ) (B : ℝ) (z : ℂ) :
      referenceShiftBlock A B z=((B⁻¹ : ℝ) : ℂ) • matrixShift A z := by
    simp only [referenceShiftBlock,matrixShift,smul_sub,smul_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  have hκ2 : 2 ≤ κ := le_max_left _ _
  have hκ : 0 < κ := by linarith
  have hκ1 : κ⁻¹ ≤ 1 := (inv_le_one₀ hκ).mpr (by linarith)
  have hi : κ⁻¹ ≤ r / B := by
    have hh := (inv_le_inv₀ hκ (div_pos hB hr)).mpr (le_max_right 2 (B / r))
    simpa only [inv_div] using hh
  have hsing (i : Fin (Fintype.card I)) : κ⁻¹ ≤ matrixSingularValues S i := by
    apply hi.trans
    have hh := normalized_matrixShift_lower_bound A z B r hB hsep (rightSingularBasis S i)
    rw [← reference_shift_eq] at hh
    change (r / B) * ‖rightSingularBasis S i‖ ≤ ‖S.toEuclideanLin (rightSingularBasis S i)‖ at hh
    simpa only [norm_rightSingularBasis, norm_apply_rightSingularBasis, mul_one] using hh
  have hc : ((B⁻¹ : ℝ) : ℂ) * (B : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hB.ne', Complex.ofReal_one]
  have hforward : S * ((B : ℂ) • matrixResolvent A z) = 1 := by
    dsimp only [S]
    rw [reference_shift_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A z r hr hsep).1, hc, one_smul]
  have hbackward : ((B : ℂ) • matrixResolvent A z) * S = 1 := by
    dsimp only [S]
    rw [reference_shift_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A z r hr hsep).2, mul_comm (B : ℂ), hc, one_smul]
  have hpseudo : matrixPseudoinverse S = (B : ℂ) • matrixResolvent A z :=
    matrixPseudoinverse_eq_of_twoSidedInverse S _ hforward hbackward
  have htail := reciprocalMatrixApprox_error_le S (inv_pos.mpr hκ) hκ1
    (fun i => (matrixSingularValues_le_spectralNorm _ i).trans hS)
    (fun i _ => hsing i) b
  rw [← leftDefectNeumann_eq_reciprocalMatrixApprox, hpseudo] at htail
  have ht : ((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann S b - matrixResolvent A z =
      ((B⁻¹ : ℝ) : ℂ) • (leftDefectNeumann S b - (B : ℂ) • matrixResolvent A z) := by
    rw [smul_sub, smul_smul, hc, one_smul]
  have htail' : ‖((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann S b - matrixResolvent A z‖ ≤
      reciprocalError κ⁻¹ b / B := by
    rw [ht, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hB)]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hB.le)
  have herr : ‖((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann X b - matrixResolvent A z‖ ≤
      ((b : ℝ)^2 * (nativeCoefficientError ps p slack α B z+e/B) + reciprocalError κ⁻¹ b) / B := by
    have hdecomp : ((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann X b - matrixResolvent A z =
        ((B⁻¹ : ℝ) : ℂ) • (leftDefectNeumann X b - leftDefectNeumann S b) +
          (((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann S b - matrixResolvent A z) := by
      rw [smul_sub]
      abel
    rw [hdecomp]
    calc
      _ ≤ ‖((B⁻¹ : ℝ) : ℂ) • (leftDefectNeumann X b - leftDefectNeumann S b)‖ +
          ‖((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann S b - matrixResolvent A z‖ := norm_add_le _ _
      _ ≤ B⁻¹ * ((b : ℝ)^2 * (nativeCoefficientError ps p slack α B z+e/B)) +
          reciprocalError κ⁻¹ b / B := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
        exact add_le_add (mul_le_mul_of_nonneg_left hpoly (inv_nonneg.mpr hB.le)) htail'
      _ = _ := by rw [add_div]; ring
  exact ⟨hw.1, hw.2.1, herr, hw.2.2⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
