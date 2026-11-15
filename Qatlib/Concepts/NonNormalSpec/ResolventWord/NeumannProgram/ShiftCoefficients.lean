/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
public import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev ShiftSlot := Bool × Fin 4
def shiftSeed :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot := (false, 0)
def shiftSlack (z : ℂ) (α B : ℝ) : ℝ := B - α - ‖z‖
def shiftCoefficient (z : ℂ) (α B : ℝ) (s : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot) : ℂ :=
  if s.1 then ![-(α : ℂ), 0, 0, 0] s.2 else
    ![z, ((Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlack z α B / 2 : ℝ) : ℂ), -((Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlack z α B / 2 : ℝ) : ℂ), 0] s.2

def shiftSlotMatrix {H : Type} [DecidableEq H] (U : Matrix H H ℂ) (s : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot) :
    Matrix H H ℂ := if s.1 then U else 1

/-- The shift coefficients combine the slot matrices into the scalar shift of the identity minus
the scaled oracle. -/
theorem shifted_coefficient_sum (z : ℂ) (α B : ℝ)
    (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) :
    (∑ s : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient z α B s • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix U s) =
      z • (1 : Matrix H H ℂ) - (α : ℂ) • U := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_four,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix, neg_smul, sub_eq_add_neg]
  abel

/-- Under the scale and shift bound, the shift coefficient mass equals `B`. -/
theorem shift_coefficient_mass (z : ℂ) (α B : ℝ)
    (hα : 0 ≤ α) (hbound : α + ‖z‖ ≤ B) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient z α B) = B := by
  have hs :
      0 ≤ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlack z α B := by unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlack; linarith
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass, Fintype.sum_prod_type, Fin.sum_univ_four,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hα, abs_of_nonneg hs]
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlack
  ring

/-- The shifted LCU corner equals the shifted matrix divided by the positive coefficient mass
`B`. -/
theorem shifted_lcu_compress (H : Type) [Fintype H] [DecidableEq H]
    (z : ℂ) (α B : ℝ) (U : Matrix H H ℂ)
    (hα : 0 ≤ α) (hB : 0 < B) (hbound : α + ‖z‖ ≤ B) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.LCU.prepareLift (Qatlib.Foundations.PureStateMath.Ket Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient z α B) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix U) Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed)
      (Qatlib.Concepts.BlockEncoding.LCU.prepareLift (Qatlib.Foundations.PureStateMath.Ket Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed)) =
      ((B⁻¹ : ℝ) : ℂ) • (z • (1 : Matrix H H ℂ) - (α : ℂ) • U) := by
  have hm :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shift_coefficient_mass z α B hα hbound
  have hp :
      0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient z α B) := by rw [hm]; exact hB
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary_compress _ _ _ hp, hm,
      ← Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shifted_coefficient_sum z α B H U]
  simp only [Finset.smul_sum, smul_smul, Complex.ofReal_inv, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts
