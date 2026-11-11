/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeNeumannEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Multi-node Neumann encoding of the actual original oracle word. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix


variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for multinode Full Encoding Branch Dec Eq in the native multi node full encoding model. -/
local instance multinodeFullEncodingBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

/-- The actual finite word or frame satisfies `encoding_decEq_transport` with all displayed legality, input and workspace hypotheses. -/
private theorem encoding_decEq_transport {D X : Type} [Fintype D] [DecidableEq X]
    (d₁ d₂ : DecidableEq D) (M : Matrix X X ℂ) (Q : Matrix D D ℂ)
    (cs : List (AdjointStep D)) (F : Matrix D X ℂ) :
    @ProjectedUnitaryEncoding D X X _ d₁ _ _ M (@evaluate D _ d₁ Q cs) F F →
    @ProjectedUnitaryEncoding D X X _ d₂ _ _ M (@evaluate D _ d₂ Q cs) F F := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact id

/-- The complete shared word encodes the Neumann polynomial of the selected
actual blocks, using the original oracle and the common original frame. -/
theorem nativeMultiNodeNeumann_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (select (fun j =>
        identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
          (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A)) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
        (nativeMultiNodeNeumannWord b hb F ps p slack))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F)) ∧
    adjointQueryCount (nativeMultiNodeNeumannWord b hb F ps p slack) = 2*b-1 := by
  let V : J → Matrix (Reg 6 × H) (Reg 6 × H) ℂ := fun j =>
    evaluate (nativeDataQuery U) (nativeExpandedBodyWord (H := H) (ps j) (p j) (slack j))
  have hv : ∀ j, V j ∈ unitaryGroup (Reg 6 × H) ℂ := by
    intro j
    exact (native_original_input_encoding (ps j) (p j) (slack j) A U F α hbe).unitary
  have hu : select V ∈ unitaryGroup (J × (Reg 6 × H)) ℂ :=
    Qatlib.Concepts.BlockEncoding.LCU.select_unitary V hv
  have hf := nativeMultiNodeFrame_isometry (J := J) F hbe.left_isometry
  have hpoly := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding b hb (select V) (nativeMultiNodeFrame (J := J) F) hu hf
  have hblock := nativeMultiNodeFrame_compress_native (J := J) F A U α hbe ps p slack
  change compress (nativeMultiNodeFrame (J := J) F) (select V)
    (nativeMultiNodeFrame (J := J) F) = _ at hblock
  rw [hblock] at hpoly
  have hw := nativeMultiNodeNeumann_evaluate_cost b hb F ps p slack U
  refine ⟨?_, hw.2.1⟩
  rw [hw.1]
  let D := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))
  let Q : Matrix D D ℂ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (select V)
  let cs : List (AdjointStep D) :=
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector (nativeMultiNodeFrame (J := J) F))
  exact encoding_decEq_transport (instDecidableEqProd : DecidableEq D)
    (inferInstance : DecidableEq D) _ Q cs _ hpoly

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
