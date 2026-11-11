/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems

/-! Weighted error of actual native Neumann blocks. This is an operator
inequality only: it does not construct or certify a weighted quantum circuit. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

omit [DecidableEq J] in
/-- The common source, common truncation length, and common scale give a
weighted resolvent error without assuming the desired aggregate estimate.
Weights may vanish and the label or data space may be empty. -/
theorem native_weighted_gap_error
    (b : ℕ) (hb : 0 < b)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (weights : J → ℂ)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B : ℝ) (r K : J → ℝ) (z : J → ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : ∀ j, α + ‖z j‖ ≤ B)
    (hr : ∀ j, 0 < r j)
    (hsep : ∀ j w, w ∈ matrixNumericalRange A → r j ≤ ‖z j-w‖)
    (hK : ∀ j, jointResolventCondition B (r j) ≤ K j)
    (hsmall : ∀ j, nativeCoefficientError (ps j) (p j) (slack j) α B (z j) ≤
      1/(4*(K j)^2)) :
    ‖(∑ j, weights j • (((B⁻¹ : ℝ) : ℂ) •
        Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock (ps j) (p j) (slack j) A α) b)) -
      (∑ j, weights j • matrixResolvent A (z j))‖ ≤
      ∑ j, ‖weights j‖ *
        (((2*(K j)^2+4*(K j)^3) *
          nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
          reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B) := by
  have hnode (j : J) :
      ‖((B⁻¹ : ℝ) : ℂ) •
        Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock (ps j) (p j) (slack j) A α) b -
          matrixResolvent A (z j)‖ ≤
      ((2*(K j)^2+4*(K j)^3) *
        nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
        reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B := by
    exact (native_original_neumann_resolvent_gap b hb (ps j) (p j) (slack j)
      A U F α B (r j) (K j) (z j) hbe hB (hbound j) (hr j)
      (fun w hw => hsep j w hw) (hK j) (hsmall j)).2.2.1
  simp only [← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ ≤ ∑ j, ‖weights j •
        ((((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
          (nativeShiftBlock (ps j) (p j) (slack j) A α) b) -
            matrixResolvent A (z j))‖ := norm_sum_le _ _
    _ = ∑ j, ‖weights j‖ * ‖(((B⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
          (nativeShiftBlock (ps j) (p j) (slack j) A α) b) -
            matrixResolvent A (z j)‖ := by
      exact Finset.sum_congr rfl (fun j _ => norm_smul _ _)
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hnode j) (norm_nonneg _))

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
