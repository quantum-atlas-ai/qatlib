/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeDataBody
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding

/-! Actual native coefficients versus the single-node normalized shift.
The result is conditional on coefficient errors; it does not synthesize parameters. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords


open Qatlib Matrix
open scoped Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The estimate `affine_contraction_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem affine_contraction_error (C : Matrix I I ℂ) (hC : ‖C‖ ≤ 1)
    (a c s t : ℂ) :
    ‖(a • (1 : Matrix I I ℂ) + c • C) - (s • 1 + t • C)‖ ≤ ‖a-s‖ + ‖c-t‖ := by
  have heq : (a • (1 : Matrix I I ℂ) + c • C) - (s • 1 + t • C) =
      (a-s) • (1 : Matrix I I ℂ) + (c-t) • C := by
    simp only [sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(a-s) • (1 : Matrix I I ℂ)‖ + ‖(c-t) • C‖ := norm_add_le _ _
    _ = ‖a-s‖ * ‖(1 : Matrix I I ℂ)‖ + ‖c-t‖ * ‖C‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖a-s‖ + ‖c-t‖ := by
      have h1 := mul_le_mul_of_nonneg_left (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I)) (norm_nonneg (a-s))
      have h2 := mul_le_mul_of_nonneg_left hC (norm_nonneg (c-t))
      linarith

/-- The very same native circuit encodes its actual affine block, whose
distance to `(zI-A)/B` is bounded solely by its two scalar coefficient errors.
The original input is a zero-error common-frame encoding, with no normality
assumption; no finite-precision parameter-generation claim is made. -/
theorem native_original_shift_coefficient_error
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (α B : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α 0) :
    ProjectedUnitaryEncoding
      (identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
        (oracleCoefficient ps p slack / (α : ℂ)) • A)
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))
      (nativeDataFrame F) (nativeDataFrame F) ∧
    ‖(identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
        (oracleCoefficient ps p slack / (α : ℂ)) • A) -
      ((z / (B : ℂ)) • 1 - ((B : ℂ)⁻¹) • A)‖ ≤
      ‖identityCoefficient ps p slack - z / (B : ℂ)‖ +
        ‖oracleCoefficient ps p slack + (α : ℂ) / (B : ℂ)‖ := by
  refine ⟨native_original_input_encoding ps p slack A U F α hbe, ?_⟩
  have hAreal : A = α • compress F U F := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm hbe.error_le (norm_nonneg _)))
  have hA : A = (α : ℂ) • compress F U F := by
    rwa [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hAreal
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast hbe.normalization_pos.ne'
  have hc : ‖compress F U F‖ ≤ 1 :=
    Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one hbe.left_isometry hbe.unitary hbe.right_isometry
  have hactual : (oracleCoefficient ps p slack / (α : ℂ)) • A =
      oracleCoefficient ps p slack • compress F U F := by
    rw [hA, smul_smul, div_mul_cancel₀ _ hα]
  have hideal : ((B : ℂ)⁻¹) • A = ((α : ℂ) / (B : ℂ)) • compress F U F := by
    rw [hA, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  rw [hactual, hideal]
  simpa only [sub_eq_add_neg, neg_smul, sub_neg_eq_add, neg_neg] using
    (affine_contraction_error (compress F U F) hc
      (identityCoefficient ps p slack) (oracleCoefficient ps p slack)
      (z / (B : ℂ)) (-((α : ℂ) / (B : ℂ))))

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
