/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodePerLabel
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeRelabel
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Candidate bridge from a diagonal clean block to a weighted LCU. The
actual whole-space operator is not assumed to be a label-diagonal SELECT. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The finite construction in `NativeCleanBlockLCU` satisfies `fiber_frame_apply` under the displayed hypotheses. -/
private theorem fiber_frame_apply {K L M : Type} [Fintype L] [DecidableEq K] [DecidableEq L]
    (k₀ : K) (F : Matrix L M ℂ) (k : K) (l : L) (m : M) :
    (encodingFiber (I := L) k₀ * F) (k,l) m = if k = k₀ then F l m else 0 := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · by_cases hk : k = k₀ <;> simp [encodingFiber, hk]
  · intro x _ hx
    simp [encodingFiber, Ne.symm hx]
  · simp

omit [Fintype I] [DecidableEq I] in
/-- Moving the node label to the outside also moves the actual joint frame to
the tensor of the untouched label and the original single-node frame. -/
theorem relabeled_neumann_frame (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ) :
    Matrix.reindex (nativeMultiNodeLabelEquiv (J := J) (H := H) b) (Equiv.refl (J × I))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F)) =
        (1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F) := by
  classical
  ext ⟨j, flags, slot, x⟩ ⟨l, i⟩
  simp [Matrix.reindex_apply, nativeMultiNodeLabelEquiv, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame, fiber_frame_apply, nativeMultiNodeFrame,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

omit [Fintype H] [DecidableEq H] in
/-- The finite construction in `NativeCleanBlockLCU` satisfies `label_frame_fiber` under the displayed hypotheses. -/
private theorem label_frame_fiber (F : Matrix H I ℂ) (j₀ : J) :
    tagFrame j₀ F =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * encodingFiber (I := I) j₀ := by
  classical
  ext ⟨j,h⟩ i
  rw [Matrix.mul_apply, Finset.sum_eq_single (j₀,i)]
  · simp [tagFrame, encodingFiber_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    simp [encodingFiber_apply, hx]
  · simp

/-- The finite construction in `NativeCleanBlockLCU` satisfies `label_prepare_intertwine` under the displayed hypotheses. -/
private theorem label_prepare_intertwine (F : Matrix H I ℂ) (P : Matrix J J ℂ) :
    prepareRegister (I := H) P * ((1 : Matrix J J ℂ) ⊗ₖ F) =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * prepareRegister (I := I) P := by
  simp only [prepareRegister, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

omit [Fintype J] [Fintype I] in
/-- The finite construction in `NativeCleanBlockLCU` satisfies `diagonal_phase_select` under the displayed hypotheses. -/
private theorem diagonal_phase_select (d : J → ℂ) :
    prepareRegister (I := I) (Matrix.diagonal (fun j => coefficientPhase (d j))) =
      select (phaseAbsorbed d (fun _ => (1 : Matrix I I ℂ))) := by
  ext ⟨j,i⟩ ⟨k,l⟩
  by_cases hj : j = k <;> by_cases hi : i = l <;>
    simp [prepareRegister, Matrix.kroneckerMap_apply,
      select, phaseAbsorbed, Matrix.one_apply, hj, hi]


end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
