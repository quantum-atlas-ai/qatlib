/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeDataBody
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.OriginalUniformNeumann
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! The complete original-query Neumann word for arbitrary data and the
original exact common frame. Outer known matrix macros remain separately charged. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Construction for native Original Neumann Word in the native data neumann model. -/
def nativeOriginalNeumannWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    List (AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H)))) :=
  substituteAdjointCircuit
    (phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (nativeExpandedBodyWord (H := H) ps p slack))
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector (nativeDataFrame F)))

omit [Fintype H] in
/-- The finite construction in `NativeDataNeumann` satisfies `data_lift_one` under the displayed hypotheses. -/
private theorem data_lift_one (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle (H := Reg 6 × H) b 1 = 1 := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, parallelOracle, parallel_select_one,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, TensorGate, Matrix.one_kronecker_one]

/-- The finite construction in `NativeDataNeumann` satisfies `data_lift_mul` under the displayed hypotheses. -/
private theorem data_lift_mul (b : ℕ) (U V : Matrix (Reg 6 × H) (Reg 6 × H) ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (U*V) = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U * Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_mul, Matrix.one_mul,
    parallelOracle, parallel_select_mul]

/-- The finite construction in `NativeDataNeumann` satisfies `data_lift_adjoint` under the displayed hypotheses. -/
private theorem data_lift_adjoint (b : ℕ) (U : Matrix (Reg 6 × H) (Reg 6 × H) ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b Uᴴ = (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U)ᴴ := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_conjTranspose,
    Matrix.conjTranspose_one, parallelOracle, parallel_select_adjoint]

/-- The actual finite word or frame satisfies `data_lift_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem data_lift_unitary (b : ℕ) (U : Matrix (Reg 6 × H) (Reg 6 × H) ℂ)
    (hU : U ∈ unitaryGroup (Reg 6 × H) ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U ∈
      unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) ℂ :=
  tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))

/-- Same original A/U/F input, actual emitted word and exact mixed ledger.
No normality, free shifted oracle or abstract coefficient preparation is assumed. -/
theorem native_original_neumann_encoding (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α : ℝ) (hbe : BlockEncoding A U F F α 0) :
    WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
        (identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
          (oracleCoefficient ps p slack / (α : ℂ)) • A) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))
        (nativeOriginalNeumannWord b hb F ps p slack))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)) ∧
    adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
      2*b + (2*b-1)*(436+(if slack then 1 else 0)) := by
  have hinput := native_original_input_encoding ps p slack A U F α hbe
  let W := evaluate (nativeDataQuery U) (nativeExpandedBodyWord (H := H) ps p slack)
  let P := rangeProjector (nativeDataFrame F)
  let cs := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P
  let body := phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (nativeExpandedBodyWord (H := H) ps p slack)
  have hp : IsOrthogonalProjector P := rangeProjector_isOrthogonalProjector hinput.left_isometry
  obtain ⟨hcq,hcg,hcw⟩ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb P
  obtain ⟨hrawq,hrawg⟩ := nativeExpandedBody_cost (H := H) ps p slack
  have hbq : adjointQueryCount body = 1 := (phaseLiftWord_counts _ _).1.trans hrawq
  have hbg : adjointGateCount body = 436+(if slack then 1 else 0) :=
    (phaseLiftWord_counts _ _).2.trans hrawg
  have hbw : WellFormedAdjointCircuit body := phaseLiftWord_wellFormed
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (data_lift_unitary b) (nativeExpandedBody_legal ps p slack)
  have hlift := phaseLiftWord_evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (data_lift_one b)
    (data_lift_mul b) (data_lift_adjoint b)
    (nativeDataQuery U) (nativeExpandedBodyWord (H := H) ps p slack)
  obtain ⟨he,hq,hg,hw⟩ := substitute_adjoint_evaluate_cost
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)) body cs
  have ht : evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))
      (nativeOriginalNeumannWord b hb F ps p slack) =
      evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b W) cs := by
    change evaluate _ (substituteAdjointCircuit body cs) = _
    rw [he, hlift]
  have hpoly := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding b hb W (nativeDataFrame F)
    hinput.unitary hinput.left_isometry
  rw [hinput.encoded] at hpoly
  refine ⟨hw hbw (hcw hp), ?_, ?_, ?_⟩
  · rw [ht]
    exact hpoly
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [hq, hcq, hbq, Nat.mul_one]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [hg, hcg, hcq, hbg]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
