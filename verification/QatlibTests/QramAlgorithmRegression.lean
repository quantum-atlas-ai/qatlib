/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Papers.QRecommender16.Recommendations.ThresholdSampling
import Qatlib.Papers.QCNN20.Forward.Convolution
import Qatlib.Papers.QCNN20.Backprop.Gradients
import Qatlib.Papers.QFVMChen22.TimeStep.SparseCorrection
import Mathlib.Tactic.NormNum

/-!
# Regression tests for QRAM algorithms

These examples check vacant entries, signed amplitude preparation, patch
alias updates, and residual consistency under sparse writeback for the QRAM
constructions used in [KerenidisPrakash2017], [KerenidisLandmanPrakash2020],
and [ChenXueChenEtAl2022].
-/

set_option autoImplicit false

namespace QatlibTests.QramAlgorithmRegression

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Papers.QRecommender16.QramMatrix

private def left : Address 1 := fun _ => false
private def right : Address 1 := fun _ => true

/-- Writing one entry of an initially vacant matrix keeps another entry zero. -/
example :
    entry (writeEntry (rows := 1) (columns := 1) (.vacant 2) left right (-3)) left left = 0 := by
  have h : left ≠ right := fun hEq => by
    have hBit := congrFun hEq (0 : Fin 1)
    simp [left, right] at hBit
  have hOther : ¬ (left = left ∧ left = right) := fun hPair => h hPair.2
  calc
    _ = entry (.vacant 2) left left :=
      (entry_after_write _ _ _ _ _ _).trans (ite_eq_right hOther)
    _ = 0 := rfl

/-- An unoccupied branch still has amplitude zero after a signed value is written elsewhere. -/
example : pathAmplitude (write (.vacant 1 : Tree ℝ 1) right (-3)) left = 0 := by
  have h : left ≠ right := fun hEq => by
    have hBit := congrFun hEq (0 : Fin 1)
    simp [left, right] at hBit
  have hValid : Valid (write (.vacant 1 : Tree ℝ 1) right (-3)) :=
    valid_write _ _ _ (by trivial)
  have hRead : Qatlib.Foundations.QramData.SquaredNormTree.read
      (.vacant 1 : Tree ℝ 1) left = 0 := rfl
  simp only [path_amplitude_eq _ hValid, read_write, ite_eq_right h, hRead, zero_div]

/-- A next-layer pixel write updates all its aliases in the im2col table. -/
example (layout : Qatlib.Papers.QCNN20.PatchMemory.Layout Bool 1 1)
    (memory : Tree ℝ 2) (slot : Address 2) (h : layout.pixelAt slot = true) :
    read (Qatlib.Papers.QCNN20.PatchMemory.scatterPixel layout memory true 2) slot = 2 := by
  rw [Qatlib.Papers.QCNN20.PatchMemory.read_scatter_pixel]
  simp [h]

open Qatlib.Papers.QFVMChen22.QramStorage
open Qatlib.Papers.QFVMChen22.TimeStep

/-- A sparse solver step preserves agreement between physical variables and all residuals. -/
example (geometry : Geometry 1)
    (localRhs : Address 1 → (Fin geometry.stencilSize → ℝ) → ℝ)
    (physical : Address 1 → ℝ) :
    Consistent geometry localRhs (applyCorrection geometry localRhs 2 [(right, 3)]
      (initializeSnapshot geometry localRhs physical)) :=
  consistent_apply_correction _ _ _ _ _ (consistent_initialize _ _ _)

end QatlibTests.QramAlgorithmRegression
