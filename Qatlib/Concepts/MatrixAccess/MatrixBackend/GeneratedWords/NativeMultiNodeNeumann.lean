/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeBody
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
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! A finite-node Neumann word using one shared controlled data oracle.
Node selection and the outer preparation are known matrix macros. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for multinode Neumann Branch Dec Eq in the native multi node neumann model. -/
local instance multinodeNeumannBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

/-- A common original data frame extended to preserve the node register. -/
def nativeMultiNodeFrame (F : Matrix H I ℂ) : Matrix (J × (Reg 6 × H)) (J × I) ℂ :=
  (1 : Matrix J J ℂ) ⊗ₖ nativeDataFrame F

/-- Extending the original common frame by an untouched label is isometric. -/
theorem nativeMultiNodeFrame_isometry (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (nativeMultiNodeFrame (J := J) F) := by
  have hf := nativeDataFrame_isometry F hF
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry nativeMultiNodeFrame
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  change ((1 : Matrix J J ℂ)ᴴ * 1) ⊗ₖ ((nativeDataFrame F)ᴴ * nativeDataFrame F) = 1
  rw [Matrix.conjTranspose_one, Matrix.one_mul, hf, Matrix.one_kronecker_one]

/-- A full fresh-flag Neumann word obtained by substituting the actual
node-selecting body into every query site. The word uses common F and U. -/
def nativeMultiNodeNeumannWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    List (AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H))))) :=
  substituteAdjointCircuit
    (phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (nativeMultiNodeBodyWord (H := H) ps p slack))
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector (nativeMultiNodeFrame (J := J) F)))

omit [Fintype J] [Fintype H] in
/-- The finite construction in `NativeMultiNodeNeumann` satisfies `multinode_lift_one` under the displayed hypotheses. -/
private theorem multinode_lift_one (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle (H := J × (Reg 6 × H)) b 1 = 1 := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, parallelOracle, parallel_select_one,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, TensorGate, Matrix.one_kronecker_one]
  ext x y
  simp [Matrix.one_apply]

/-- The finite construction in `NativeMultiNodeNeumann` satisfies `multinode_lift_mul` under the displayed hypotheses. -/
private theorem multinode_lift_mul (b : ℕ)
    (U V : Matrix (J × (Reg 6 × H)) (J × (Reg 6 × H)) ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (U*V) = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U * Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_mul, Matrix.one_mul,
    parallelOracle, parallel_select_mul]

/-- The finite construction in `NativeMultiNodeNeumann` satisfies `multinode_lift_adjoint` under the displayed hypotheses. -/
private theorem multinode_lift_adjoint (b : ℕ)
    (U : Matrix (J × (Reg 6 × H)) (J × (Reg 6 × H)) ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b Uᴴ = (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U)ᴴ := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, tensorGate_conjTranspose,
    Matrix.conjTranspose_one, parallelOracle, parallel_select_adjoint]

omit [DecidableEq I] in
/-- The actual substituted word evaluates as the uniform Neumann word whose
oracle is the diagonal family of actual node bodies. Query count refers to the
same common controlled U (and its adjoint); selected gates remain macros. -/
theorem nativeMultiNodeNeumann_evaluate_cost (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (U : Matrix H H ℂ) :
    evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
      (nativeMultiNodeNeumannWord b hb F ps p slack) =
      evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (select (fun j =>
        evaluate (nativeDataQuery U) (nativeExpandedBodyWord (H := H) (ps j) (p j) (slack j)))))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector (nativeMultiNodeFrame (J := J) F))) ∧
    adjointQueryCount (nativeMultiNodeNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeMultiNodeNeumannWord b hb F ps p slack) =
      2*b + (2*b-1)*3 := by
  let P := rangeProjector (nativeMultiNodeFrame (J := J) F)
  let cs := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P
  let body := phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (nativeMultiNodeBodyWord (H := H) ps p slack)
  obtain ⟨hcq,hcg,_⟩ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb P
  obtain ⟨hrawq,hrawg⟩ := nativeMultiNodeBody_cost (H := H) ps p slack
  have hbq : adjointQueryCount body = 1 := (phaseLiftWord_counts _ _).1.trans hrawq
  have hbg : adjointGateCount body = 3 := (phaseLiftWord_counts _ _).2.trans hrawg
  have hlift := phaseLiftWord_evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (multinode_lift_one b)
    (multinode_lift_mul b) (multinode_lift_adjoint b)
    (parallelOracle (J := J) (nativeDataQuery U)) (nativeMultiNodeBodyWord (H := H) ps p slack)
  obtain ⟨he,hq,hg,_⟩ := substitute_adjoint_evaluate_cost
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U))) body cs
  refine ⟨?_, ?_, ?_⟩
  · change evaluate _ (substituteAdjointCircuit body cs) = _
    rw [he, hlift, nativeMultiNodeBody_evaluate]
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [hq, hcq, hbq, Nat.mul_one]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [hg, hcg, hcq, hbg]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
