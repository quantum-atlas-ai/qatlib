/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeNeumann
import Mathlib.Data.Matrix.Block
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

/-! Common-frame compression for the selected actual native node bodies. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix


variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Construction for rect Label Lift in the native multi node neumann encoding model. -/
private def rectLabelLift {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) : Matrix (L × M) (L × N) ℂ :=
  (Matrix.blockDiagonal V).submatrix (Equiv.prodComm L M) (Equiv.prodComm L N)

/-- The finite construction in `NativeMultiNodeNeumannEncoding` satisfies `rectLabelLift_adjoint` under the displayed hypotheses. -/
private theorem rectLabelLift_adjoint {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) :
    (rectLabelLift V)ᴴ = rectLabelLift (fun j => (V j)ᴴ) := by
  simp only [rectLabelLift, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

/-- The finite construction in `NativeMultiNodeNeumannEncoding` satisfies `rectLabelLift_mul` under the displayed hypotheses. -/
private theorem rectLabelLift_mul {M N P L : Type}
    [Fintype N] [Fintype L] [DecidableEq L]
    (V : L → Matrix M N ℂ) (W : L → Matrix N P ℂ) :
    rectLabelLift (fun j => V j * W j) = rectLabelLift V * rectLabelLift W := by
  unfold rectLabelLift
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

/-- The finite construction in `NativeMultiNodeNeumannEncoding` satisfies `rectLabelLift_select` under the displayed hypotheses. -/
private theorem rectLabelLift_select {L M : Type} [DecidableEq L]
    (V : L → Matrix M M ℂ) : rectLabelLift V = select V := by
  rfl

omit [Fintype J] [Fintype I] [DecidableEq I] in
/-- The finite construction in `NativeMultiNodeNeumannEncoding` satisfies `nativeMultiNodeFrame_eq_lift` under the displayed hypotheses. -/
private theorem nativeMultiNodeFrame_eq_lift (F : Matrix H I ℂ) :
    nativeMultiNodeFrame (J := J) F = rectLabelLift (fun _ : J => nativeDataFrame F) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j = k <;>
    simp [nativeMultiNodeFrame, rectLabelLift, Matrix.blockDiagonal, hj]

omit [Fintype I] [DecidableEq I] in
/-- Compression by the common original frame acts separately in every label
sector; this is a matrix identity valid also for empty label/data types. -/
theorem nativeMultiNodeFrame_compress_select (F : Matrix H I ℂ)
    (V : J → Matrix (Reg 6 × H) (Reg 6 × H) ℂ) :
    compress (nativeMultiNodeFrame (J := J) F) (select V)
      (nativeMultiNodeFrame (J := J) F) =
      select (fun j => compress (nativeDataFrame F) (V j) (nativeDataFrame F)) := by
  simp only [compress, nativeMultiNodeFrame_eq_lift, ← rectLabelLift_select,
    rectLabelLift_adjoint, ← rectLabelLift_mul]

/-- The common original oracle and frame give the exact actual native block on
every node sector, including arbitrary mixtures of slack flags. -/
theorem nativeMultiNodeFrame_compress_native (F : Matrix H I ℂ)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    compress (nativeMultiNodeFrame (J := J) F)
      (select (fun j => evaluate (nativeDataQuery U)
        (nativeExpandedBodyWord (H := H) (ps j) (p j) (slack j))))
      (nativeMultiNodeFrame (J := J) F) =
      select (fun j => identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
        (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) := by
  rw [nativeMultiNodeFrame_compress_select]
  apply congrArg select
  funext j
  exact (native_original_input_encoding (ps j) (p j) (slack j) A U F α hbe).encoded

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
