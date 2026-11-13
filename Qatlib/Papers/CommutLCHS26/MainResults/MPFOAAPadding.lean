/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAChoice
import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification

/-!
# Padding encodings to the amplification amplitude

This module adds an auxiliary two-dimensional rotation to change an inverse-mass encoding into
an encoding scaled by the selected amplification sine. It gives both matrix and circuit forms,
including exact evaluation, gate counts, and preservation of circuit well-formedness for the
multi-product implementation associated with [AftabAnTrivisa2026].

## Main statements

* `padded_encoding`: proves the padded projected encoding.
* `body_counts`: shows that padding adds one gate and no oracle queries.
* `body_encoding`: transfers the encoding to the padded circuit body.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAPadding

open Matrix
open scoped Classical Matrix.Norms.L2Operator
open MPFOAAChoice
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The two-dimensional padding rotation with corner amplitude A sin(π/(2 queries A)). -/
def rotation (A : ℝ) : Matrix Bool Bool ℂ :=
  scaleEightRotation (A * Real.sin (angle (queries A)))

/-- For A ≥ 1, the selected padding rotation is unitary. -/
theorem rotation_unitary (A : ℝ) (hA : 1 ≤ A) : rotation A ∈ unitaryGroup Bool ℂ := by
  apply scaleEightRotation_unitary
  rw [abs_of_nonneg (mul_nonneg (by linarith) (sin_pos _ (queries_pos A)).le)]
  exact selected_admissible A

/-- The false-false corner of the padding rotation is A times the selected sine amplitude. -/
theorem rotation_corner (A : ℝ) :
    rotation A false false = (A * Real.sin (angle (queries A)) : ℝ) := rfl

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Tensoring an inverse-mass encoding with the padding rotation gives a projected encoding
scaled by the selected sine amplitude. -/
theorem padded_encoding (A : ℝ) (hA : 1 ≤ A) (C : Matrix I I ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (h : ProjectedUnitaryEncoding ((A : ℂ)⁻¹ • C) U R R) :
    ProjectedUnitaryEncoding ((Real.sin (angle (queries A)) : ℂ) • C)
      (TensorGate (rotation A) U) (scaleEightFrame R) (scaleEightFrame R) := by
  refine ⟨tensorGate_unitary (rotation_unitary A hA) h.unitary,
    scaleEightFrame_isometry R h.left_isometry, scaleEightFrame_isometry R h.right_isometry, ?_⟩
  rw [scaleEightFrame_compress, rotation_corner, h.encoded, smul_smul]
  have hn : (A : ℂ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by linarith)
  congr 1
  push_cast
  field_simp

omit [Fintype H] [Fintype I] [DecidableEq I] in

/-- The lifted circuit followed by a single auxiliary padding-rotation gate. -/
def body (A : ℝ) (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  cs.map scaleEightLiftStep ++ [.gate (TensorGate (rotation A) 1)]

omit [Fintype H] [Fintype I] [DecidableEq I] in

/-- Padding a circuit preserves its oracle query count and adds exactly one gate. -/
theorem body_counts (A : ℝ) (cs : List (AdjointStep H)) :
    adjointQueryCount (body A cs) = adjointQueryCount cs ∧
    adjointGateCount (body A cs) = adjointGateCount cs + 1 := by
  have hm : adjointQueryCount (cs.map scaleEightLiftStep) = adjointQueryCount cs ∧
      adjointGateCount (cs.map scaleEightLiftStep) = adjointGateCount cs := by
    induction cs with
    | nil => exact ⟨rfl, rfl⟩
    | cons c cs ih => cases c <;> simp [scaleEightLiftStep, adjointQueryCount, adjointGateCount, ih]
  simp [body, adjointQueryCount_append, adjointGateCount_append, adjointQueryCount,
      adjointGateCount, hm]

omit [Fintype I] [DecidableEq I] in

/-- Evaluating the lifted circuit with the lifted oracle equals the tensor lift of its original
evaluation. -/
theorem lift_evaluate (O : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (cs.map scaleEightLiftStep) =
      TensorGate (1 : Matrix Bool Bool ℂ) (evaluate O cs) := by
  induction cs with
  | nil => simp [evaluate, tensorGate_one]
  | cons c cs ih => cases c <;> simp [List.map_cons, scaleEightLiftStep, evaluate, instructionMatrix,
      ih, tensorGate_conjTranspose, tensorGate_mul]

omit [Fintype I] [DecidableEq I] in

/-- The padded circuit evaluates to the tensor product of the padding rotation and the original
circuit evaluation. -/
theorem body_evaluate (O : Matrix H H ℂ) (A : ℝ) (cs : List (AdjointStep H)) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (body A cs) =
      TensorGate (rotation A) (evaluate O cs) := by
  rw [body, evaluate_append, lift_evaluate]
  simp [evaluate, instructionMatrix, tensorGate_mul]

omit [Fintype I] [DecidableEq I] in

/-- Lifting every circuit step to the auxiliary space preserves well-formedness. -/
theorem lift_wellFormed (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (cs.map scaleEightLiftStep) := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons, scaleEightLiftStep,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
      WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨tensorGate_unitary (Submonoid.one_mem _) hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

omit [Fintype I] [DecidableEq I] in

/-- For A ≥ 1, padding a well-formed circuit yields a well-formed circuit. -/
theorem body_wellFormed (A : ℝ) (hA : 1 ≤ A) (cs : List (AdjointStep H))
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (body A cs) := by
  apply (lift_wellFormed cs hcs).append
  exact (WellFormedAdjointCircuit.gate_cons_iff _ _).2
    ⟨tensorGate_unitary (rotation_unitary A hA) (Submonoid.one_mem _), .nil⟩

/-- An inverse-mass encoding implemented by a circuit becomes a sine-scaled projected encoding
after circuit padding. -/
theorem body_encoding (O : Matrix H H ℂ) (A : ℝ) (hA : 1 ≤ A)
    (C : Matrix I I ℂ) (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (h : ProjectedUnitaryEncoding ((A : ℂ)⁻¹ • C) (evaluate O cs) R R) :
    ProjectedUnitaryEncoding ((Real.sin (angle (queries A)) : ℂ) • C)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (body A cs))
      (scaleEightFrame R) (scaleEightFrame R) := by
  rw [body_evaluate]
  exact padded_encoding A hA C _ R h

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAPadding
