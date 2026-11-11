/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftError
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannStability
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeDataNeumann
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

/-! Conditional same-input consumer of the native shift and Neumann error.
The ideal shift is explicitly assumed contractive here. Parameter synthesis,
resolvent truncation, frame synthesis, and primitive gate costs are separate. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Construction for native Shift Block in the native neumann consumer model. -/
def nativeShiftBlock (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (A : Matrix I I ℂ) (α : ℝ) : Matrix I I ℂ :=
  identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
    (oracleCoefficient ps p slack / (α : ℂ)) • A

/-- Construction for reference Shift Block in the native neumann consumer model. -/
def referenceShiftBlock (A : Matrix I I ℂ) (B : ℝ) (z : ℂ) : Matrix I I ℂ :=
  (z / (B : ℂ)) • 1 - ((B : ℂ)⁻¹) • A

/-- Construction for native Coefficient Error in the native neumann consumer model. -/
def nativeCoefficientError (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (α B : ℝ) (z : ℂ) : ℝ :=
  ‖identityCoefficient ps p slack - z / (B : ℂ)‖ +
    ‖oracleCoefficient ps p slack + (α : ℂ) / (B : ℂ)‖

/-- One original input and one emitted circuit give the encoded actual
Neumann block, its conditional error against the ideal shift polynomial, and
the exact original-query and mixed known-instruction ledger. -/
theorem native_neumann_shift_error_consumer
    (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B : ℝ) (z : ℂ) (hbe : BlockEncoding A U F F α 0)
    (hideal : ‖referenceShiftBlock A B z‖ ≤ 1) :
    WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock ps p slack A α) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))
        (nativeOriginalNeumannWord b hb F ps p slack))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)) ∧
    ‖((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock ps p slack A α) b -
      ((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (referenceShiftBlock A B z) b‖ ≤
      ‖(b : ℂ)⁻¹‖ * ((b : ℝ)^2 * nativeCoefficientError ps p slack α B z) ∧
    adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
      2*b + (2*b-1)*(436+(if slack then 1 else 0)) := by
  have hs := native_original_shift_coefficient_error ps p slack A U F α B z hbe
  have hactual : ‖nativeShiftBlock ps p slack A α‖ ≤ 1 := by
    change ‖identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
      (oracleCoefficient ps p slack / (α : ℂ)) • A‖ ≤ 1
    rw [← hs.1.encoded]
    exact (compress_norm_le hs.1.left_isometry hs.1.right_isometry _).trans
      (unitary_norm_le_one hs.1.unitary)
  have hcoeff : ‖nativeShiftBlock ps p slack A α - referenceShiftBlock A B z‖ ≤
      nativeCoefficientError ps p slack α B z := by
    exact hs.2
  have hp := leftDefectNeumann_perturbation (nativeShiftBlock ps p slack A α)
    (referenceShiftBlock A B z) b hactual hideal
  have hp' : ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock ps p slack A α) b -
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (referenceShiftBlock A B z) b‖ ≤
      (b : ℝ)^2 * nativeCoefficientError ps p slack α B z :=
    hp.trans (mul_le_mul_of_nonneg_left hcoeff (sq_nonneg (b : ℝ)))
  have hw := native_original_neumann_encoding b hb ps p slack A U F α hbe
  refine ⟨hw.1, hw.2.1, ?_, hw.2.2⟩
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left hp' (norm_nonneg _)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
