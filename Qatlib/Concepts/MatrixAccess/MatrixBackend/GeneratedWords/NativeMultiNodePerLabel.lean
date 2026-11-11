/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeFullEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodePolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Per-label output of the actual original-oracle Neumann word. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix


variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for multinode Per Label Branch Dec Eq in the native multi node per label model. -/
local instance multinodePerLabelBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

omit [Fintype J] [Fintype I] [DecidableEq I] in
/-- The finite construction in `NativeMultiNodePerLabel` satisfies `select_scalar` under the displayed hypotheses. -/
private theorem select_scalar (V : J → Matrix I I ℂ) (c : ℂ) :
    c • select V = select (fun j => c • V j) := by
  ext ⟨j, x⟩ ⟨k, y⟩
  by_cases h : j = k <;> simp [select, Matrix.smul_apply, h]

/-- The physical shared word encodes the actual Neumann polynomial in each
label sector, using one common original oracle and frame. The three selected
inner gates and the outer gates remain known matrix macros. -/
theorem nativeMultiNodeNeumann_per_label (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    ProjectedUnitaryEncoding
      (select (fun j => ((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
        (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
          (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b))
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
        (nativeMultiNodeNeumannWord b hb F ps p slack))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F)) ∧
    adjointQueryCount (nativeMultiNodeNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeMultiNodeNeumannWord b hb F ps p slack) =
      2*b+(2*b-1)*3 := by
  have h := nativeMultiNodeNeumann_encoding b hb F A U α hbe ps p slack
  rw [leftDefectNeumann_select, select_scalar] at h
  exact ⟨h.1, h.2, (nativeMultiNodeNeumann_evaluate_cost b hb F ps p slack U).2.2⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
