/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Mathlib.Algebra.BigOperators.Fin
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-!
# Eight-slot coefficients for shifted blocks from a raw data oracle


The actual coefficient table and corner-block proofs are retained without
problem-specific contour or numerical-range assumptions. Padding cancels in
the value sum while its mass remains. The real and complex coefficients are
matrix-macro parameters; finite-bit production and elementary gate synthesis
are not established.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Abbreviation for Shift Slot in the shift coefficients model. -/
abbrev ShiftSlot := Bool × Fin 4
/-- Construction for shift Seed in the shift coefficients model. -/
def shiftSeed : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot := (false, 0)
/-- Construction for shift Slack in the shift coefficients model. -/
def shiftSlack (z : ℂ) (α B : ℝ) : ℝ := B - α - ‖z‖
/-- Construction for shift Coefficient in the shift coefficients model. -/
def shiftCoefficient (z : ℂ) (α B : ℝ) (s : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot) : ℂ :=
  if s.1 then ![-(α : ℂ), 0, 0, 0] s.2 else
    ![z, ((Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlack z α B / 2 : ℝ) : ℂ), -((Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlack z α B / 2 : ℝ) : ℂ), 0] s.2

/-- Construction for shift Slot Matrix in the shift coefficients model. -/
def shiftSlotMatrix {H : Type} [DecidableEq H] (U : Matrix H H ℂ) (s : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot) :
    Matrix H H ℂ := if s.1 then U else 1

/-  对消 padding 的数值恒等式无参数合法性前提，包含空矩阵空间。 -/
/-- The exact `shifted_coefficient_sum` invariant under the original hypotheses and resource conventions. -/
theorem shifted_coefficient_sum (z : ℂ) (α B : ℝ)
    (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) :
    (∑ s : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B s • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U s) =
      z • (1 : Matrix H H ℂ) - (α : ℂ) • U := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_four,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix, neg_smul, sub_eq_add_neg]
  abel

/-  padding 仍按实际系数收费；零/饱和系数端点不删。 -/
/-- The exact `shift_coefficient_mass` invariant under the original hypotheses and resource conventions. -/
theorem shift_coefficient_mass (z : ℂ) (α B : ℝ)
    (hα : 0 ≤ α) (hbound : α + ‖z‖ ≤ B) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B) = B := by
  have hs : 0 ≤ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlack z α B := by unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlack; linarith
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass, Fintype.sum_prod_type, Fin.sum_univ_four,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hα, abs_of_nonneg hs]
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlack
  ring

/-  原完整八槽 LCU 的实际角块，不输入正确目标角块。 -/
/-- The exact `shifted_lcu_compress` invariant under the original hypotheses and resource conventions. -/
theorem shifted_lcu_compress (H : Type) [Fintype H] [DecidableEq H]
    (z : ℂ) (α B : ℝ) (U : Matrix H H ℂ)
    (hα : 0 ≤ α) (hB : 0 < B) (hbound : α + ‖z‖ ≤ B) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.LCU.prepareLift (Qatlib.Foundations.PureStateMath.Ket Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U) Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed)
      (Qatlib.Concepts.BlockEncoding.LCU.prepareLift (Qatlib.Foundations.PureStateMath.Ket Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed)) =
      ((B⁻¹ : ℝ) : ℂ) • (z • (1 : Matrix H H ℂ) - (α : ℂ) • U) := by
  have hm := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shift_coefficient_mass z α B hα hbound
  have hp : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient z α B) := by rw [hm]; exact hB
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary_compress _ _ _ hp, hm, ← Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shifted_coefficient_sum z α B H U]
  simp only [Finset.smul_sum, smul_smul, Complex.ofReal_inv, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts
