/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FrameEncoding.SharedAncilla.SharedDefects
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.FrameEncoding.SharedAncilla

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
variable {F : Matrix H I ℂ}

structure SharedWordParams where

  scale : ℝ

  scale_pos : 0 < scale

  error : ℝ

  error_nonneg : 0 ≤ error

  defect : ℝ

  defect_nonneg : 0 ≤ defect

  targetNorm : ℝ

  targetNorm_nonneg : 0 ≤ targetNorm

noncomputable def combineParams {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] {F : Matrix H I ℂ} (b : GuardedSharedBlock H I F)
    (t : SharedWordParams) : SharedWordParams where
  scale := b.α * t.scale
  scale_pos := mul_pos b.α_pos t.scale_pos
  error := b.ε * t.targetNorm + b.α * t.error + (b.α * t.scale) * (b.defect * t.defect)
  error_nonneg := by
    have h1 : 0 ≤ b.ε * t.targetNorm := mul_nonneg b.ε_nonneg t.targetNorm_nonneg
    have h2 : 0 ≤ b.α * t.error := mul_nonneg (le_of_lt b.α_pos) t.error_nonneg
    have h3 : 0 ≤ b.defect * t.defect := mul_nonneg (Real.sqrt_nonneg _) t.defect_nonneg
    have h4 : 0 ≤ (b.α * t.scale) * (b.defect * t.defect) :=
      mul_nonneg (mul_nonneg (le_of_lt b.α_pos) (le_of_lt t.scale_pos)) h3
    linarith
  defect := b.defect * t.targetNorm + t.defect
  defect_nonneg := by
    have h1 : 0 ≤ b.defect * t.targetNorm :=
      mul_nonneg (Real.sqrt_nonneg _) t.targetNorm_nonneg
    linarith [t.defect_nonneg]
  targetNorm := b.Γ * t.targetNorm
  targetNorm_nonneg := mul_nonneg b.Γ_nonneg t.targetNorm_nonneg

noncomputable def wordParams {m : ℕ} {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] {F : Matrix H I ℂ} (p : Fin m → GuardedSharedBlock H I F) :
    List (Fin m) → SharedWordParams
  | [] => ⟨1, by norm_num, 0, by norm_num, 0, by norm_num, 1, by norm_num⟩
  | i :: cs => combineParams (p i) (wordParams p cs)

theorem clause3_endpoint :
    ∀ {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (F : Matrix H I ℂ) (b : GuardedSharedBlock H I F),
    ‖compress F b.U F - b.A‖ ≤ |1 - b.α| + b.ε ∧
    ‖b.U * F - F * b.A‖ * ‖b.U * F - F * b.A‖ ≤ b.defectBound ∧
    ‖sharedComplement F * b.U * F‖ ≤ b.defect ∧
    ‖Fᴴ * b.U * sharedComplement F‖ ≤ b.defect ∧
    (b.ζ = 0 → b.Γ = 1 → b.α = 1 → b.defectBound = 2 * b.ε) := by
  intro H I _ _ _ _ F b
  refine ⟨b.mismatch_le, b.defect_le, b.leak_le, b.leak_adjoint_le, ?_⟩
  intro hz hG hα
  unfold GuardedSharedBlock.defectBound GuardedSharedBlock.mismatch sharedMismatchBound
  simp only [hz, hG, hα]
  ring

end Qatlib.Concepts.AdversaryBounds.AdvDuality
