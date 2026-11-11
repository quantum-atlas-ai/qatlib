/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding
/-! Original unscaled input error is compared before the Neumann polynomial.
encodedInput names the actual oracle compression for proof only; it is not
a classical controller input or an unknown matrix installed as a known gate. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped Matrix.Norms.L2Operator
variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Construction for encoded Input in the native approx input model. -/
def encodedInput (U : Matrix H H ℂ) (F : Matrix H I ℂ) (α : ℝ) : Matrix I I ℂ :=
  α • compress F U F

/-- The finite construction in `NativeApproxInput` satisfies `encodedInput_exact` under the displayed hypotheses. -/
theorem encodedInput_exact (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α e : ℝ) (hbe : BlockEncoding A U F F α e) :
    BlockEncoding (encodedInput U F α) U F F α 0 := by
  refine ⟨hbe.unitary,hbe.left_isometry,hbe.right_isometry,hbe.normalization_pos,le_rfl,?_⟩
  simp [encodedInput]

/-- The estimate `input_norm_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem input_norm_bound (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α e : ℝ) (hbe : BlockEncoding A U F F α e) : ‖A‖≤α+e := by
  have hc := Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one hbe.left_isometry hbe.unitary hbe.right_isometry
  have hs : ‖α • compress F U F‖≤α := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hbe.normalization_pos]
    exact (mul_le_mul_of_nonneg_left hc hbe.normalization_pos.le).trans_eq (mul_one α)
  calc
    _ = ‖(A-α • compress F U F)+α • compress F U F‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-α • compress F U F‖+‖α • compress F U F‖ := norm_add_le _ _
    _ ≤ α+e := by linarith [hbe.error_le]

/-- The finite construction in `NativeApproxInput` satisfies `reference_shift_perturb` under the displayed hypotheses. -/
theorem reference_shift_perturb (A At : Matrix I I ℂ) (B e : ℝ) (z : ℂ)
    (hB : 0<B) (he : ‖At-A‖≤e) :
    ‖referenceShiftBlock At B z-referenceShiftBlock A B z‖≤e/B := by
  have hid : referenceShiftBlock At B z-referenceShiftBlock A B z=
      -((B : ℂ)⁻¹ • (At-A)) := by
    simp only [referenceShiftBlock,smul_sub]
    abel
  rw [hid,norm_neg,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left he (inv_pos.mpr hB).le

/-- The estimate `native_approx_input_shift_error` retains the actual parameter, input-error and normalization budgets. -/
theorem native_approx_input_shift_error
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (α B e : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α e) (hB : 0<B) :
    ProjectedUnitaryEncoding (nativeShiftBlock ps p slack (encodedInput U F α) α)
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))
      (nativeDataFrame F) (nativeDataFrame F) ∧
    ‖nativeShiftBlock ps p slack (encodedInput U F α) α-referenceShiftBlock A B z‖≤
      nativeCoefficientError ps p slack α B z+e/B := by
  have hself := encodedInput_exact A U F α e hbe
  have hn := native_original_shift_coefficient_error ps p slack (encodedInput U F α) U F α B z hself
  have he : ‖encodedInput U F α-A‖≤e := by simpa only [encodedInput,norm_sub_rev] using hbe.error_le
  have hp := reference_shift_perturb A (encodedInput U F α) B e z hB he
  refine ⟨hn.1,?_⟩
  calc
    _ ≤ ‖nativeShiftBlock ps p slack (encodedInput U F α) α-referenceShiftBlock (encodedInput U F α) B z‖+
        ‖referenceShiftBlock (encodedInput U F α) B z-referenceShiftBlock A B z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ nativeCoefficientError ps p slack α B z+e/B := add_le_add hn.2 hp

/-- The estimate `approximate_reference_contraction` retains the actual parameter, input-error and normalization budgets. -/
theorem approximate_reference_contraction (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α B e : ℝ) (z : ℂ) (hbe : BlockEncoding A U F F α e)
    (hB : 0<B) (hbound : α+e+‖z‖≤B) : ‖referenceShiftBlock A B z‖≤1 := by
  have hA := input_norm_bound A U F α e hbe
  have hz : ‖z • (1 : Matrix I I ℂ)‖≤‖z‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I)) (norm_nonneg z)).trans_eq (mul_one _)
  have hs : ‖matrixShift A z‖≤B := by
    change ‖z • (1 : Matrix I I ℂ)-A‖≤B
    exact (norm_sub_le _ _).trans (by linarith)
  have hid : referenceShiftBlock A B z=((B⁻¹ : ℝ) : ℂ) • matrixShift A z := by
    simp only [referenceShiftBlock,matrixShift,smul_sub,smul_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  rw [hid,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hB)]
  exact (mul_le_mul_of_nonneg_left hs (inv_pos.mpr hB).le).trans_eq (inv_mul_cancel₀ hB.ne')
end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
