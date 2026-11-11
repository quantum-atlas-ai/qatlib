/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding

/-!
# Necessary norm bound for near-two block implementations

A family of actual unitary compressions, with arbitrarily small error and
normalization approaching `2 * M` from above, forces `‖T‖ ≤ 2 * M`.
This is a necessary condition, not a Crouzeix theorem or a query algorithm.
The identification `T = f(A)` and `M = max (|f| on W(A))` is not assumed proved.
-/
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords



open scoped Matrix.Norms.L2Operator

/-- The estimate `encoded_norm_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem encoded_norm_bound
    {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {T : Matrix I I ℂ} {U : Matrix H H ℂ} {L R : Matrix H I ℂ} {α ε : ℝ}
    (h : BlockEncoding T U L R α ε) : ‖T‖ ≤ α + ε := by
  have hc := l2_norm_compress_le_one h.left_isometry h.unitary h.right_isometry
  have hs : ‖α • compress L U R‖ ≤ α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h.normalization_pos]
    exact (mul_le_mul_of_nonneg_left hc h.normalization_pos.le).trans_eq (mul_one α)
  calc
    ‖T‖ = ‖(T - α • compress L U R) + α • compress L U R‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖T - α • compress L U R‖ + ‖α • compress L U R‖ := norm_add_le _ _
    _ ≤ α + ε := by linarith [h.error_le]

/-- The estimate `norm_bound_from_all_errors` retains the actual parameter, input-error and normalization budgets. -/
private theorem norm_bound_from_all_errors
    {I : Type} [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (α : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
      (L R : Matrix (Fin n) I ℂ), BlockEncoding T U L R α ε) : ‖T‖ ≤ α := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, U, L, R, hb⟩ := h ε hε
  exact encoded_norm_bound hb

/-- Any universally accurate near-two block family forces the sharp norm bound.
The ancilla dimension and frames may depend on both eta and epsilon. -/
theorem norm_le_two_mul_of_near_two_blocks
    {I : Type} [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (M : ℝ)
    (hM : 0 < M)
    (h : ∀ η : ℝ, 0 < η → η < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
        (L R : Matrix (Fin n) I ℂ), BlockEncoding T U L R ((2 + η) * M) ε) :
    ‖T‖ ≤ 2 * M := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let η : ℝ := min (δ / M) (1 / 2)
  have hη : 0 < η := lt_min (div_pos hδ hM) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηM : η * M ≤ δ := (le_div_iff₀ hM).mp (min_le_left _ _)
  have hb := norm_bound_from_all_errors T ((2 + η) * M) (h η hη hη1)
  nlinarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
