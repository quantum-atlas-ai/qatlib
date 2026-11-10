/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.BlockEncoding.StateBlockEncoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

theorem compress_encodingFiber_blockCorner (j₀ : J) (U : Matrix (J × I) (J × I) ℂ) :
    compress (encodingFiber j₀) U (encodingFiber j₀) = BlockCorner U j₀ := by
  ext i k
  exact compress_encodingFiber_eq j₀ U i k

theorem encodingFiber_mul_mul_conjTranspose (j₀ : J) (A : Matrix I I ℂ) :
    (encodingFiber (I := I) j₀ * A : Matrix (J × I) I ℂ) *
      (encodingFiber (I := I) j₀)ᴴ = FiberEmbed j₀ A := by
  ext ⟨a, i⟩ ⟨b, k⟩
  by_cases ha : a = j₀ <;> by_cases hb : b = j₀
  all_goals simp [Matrix.mul_apply, encodingFiber, Matrix.conjTranspose_apply,
    fiberEmbed_apply, ha, hb]

theorem rangeProjector_encodingFiber (j₀ : J) :
    rangeProjector (encodingFiber (I := I) j₀) = FiberProjector j₀ := by
  rw [rangeProjector, fiberProjector_eq_fiberEmbed_one,
    ← encodingFiber_mul_mul_conjTranspose, Matrix.mul_one]

theorem IsBlockEncoding.toProjectedUnitaryEncoding
    {U : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ} {α : ℝ}
    (h : IsBlockEncoding U j₀ A α) :
    ProjectedUnitaryEncoding (((α⁻¹ : ℝ) : ℂ) • A) U
      (encodingFiber j₀) (encodingFiber j₀) :=
  ⟨h.1, encodingFiber_isIsometry j₀, encodingFiber_isIsometry j₀,
    by rw [compress_encodingFiber_blockCorner, h.2.2]⟩

theorem isBlockEncoding_iff_projectedUnitaryEncoding
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) :
    IsBlockEncoding U j₀ A α ↔ 0 < α ∧
      ProjectedUnitaryEncoding (((α⁻¹ : ℝ) : ℂ) • A) U
        (encodingFiber j₀) (encodingFiber j₀) := by
  constructor
  · intro h
    exact ⟨h.2.1, h.toProjectedUnitaryEncoding⟩
  · rintro ⟨hα, h⟩
    exact ⟨h.unitary, hα, by rw [← compress_encodingFiber_blockCorner, h.encoded]⟩

theorem isBlockEncoding_iff_blockEncoding
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) :
    IsBlockEncoding U j₀ A α ↔
      BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α 0 := by
  constructor
  · intro h
    refine ⟨h.1, encodingFiber_isIsometry j₀, encodingFiber_isIsometry j₀,
      h.2.1, le_rfl, ?_⟩
    rw [compress_encodingFiber_blockCorner, h.2.2]
    have hs : α • (((α⁻¹ : ℝ) : ℂ) • A) = A := by
      ext i k
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h.2.1.ne']
      simp
    rw [hs, sub_self, norm_zero]
  · intro h
    have hz : A - α • compress (encodingFiber j₀) U (encodingFiber j₀) = 0 :=
      norm_eq_zero.mp (le_antisymm h.error_le (norm_nonneg _))
    have heq := sub_eq_zero.mp hz
    refine ⟨h.unitary, h.normalization_pos, ?_⟩
    rw [← compress_encodingFiber_blockCorner, heq]
    ext i k
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ h.normalization_pos.ne']
    simp

theorem isProjectedEncoding_iff_blockEncoding
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ) (α : ℝ) :
    IsProjectedEncoding U j₀ A α ↔
      BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α 0 :=
  (isProjectedEncoding_iff_isBlockEncoding U j₀ A α).trans
    (isBlockEncoding_iff_blockEncoding U j₀ A α)

end Qatlib.Concepts.BlockEncoding.StateBlockEncoding
