/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.RawShiftedEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.JointResolventWord
import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral

/-! The phase-free left-defect polynomial, connected to the existing reciprocal
approximation and to the actual original-oracle resolvent input. This module
proves the matrix approximation, not correctness of the Python gate emitter. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]


/-- Unnormalized actual resolvent approximation; no desired inverse is supplied. -/
def jointNeumannResolvent {L : Type} [Fintype L] [DecidableEq L]
    (A : Matrix I I ℂ) (z : L → ℂ) (B₀ : ℝ) (b : ℕ) : Matrix (L × I) (L × I) ℂ :=
  ((B₀⁻¹ : ℝ) : ℂ) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (jointNormalizedShift A z B₀) b

/-- Original common-frame oracle inputs derive the contraction, all-mode gap
and inverse target. The output is a matrix error bound, not a circuit claim. -/
theorem original_neumann_resolvent_error
    (H I L : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α B₀ r : ℝ) (z : L → ℂ) (b : ℕ)
    (henc : BlockEncoding A U F F α 0) (hB : 0 < B₀)
    (hbound : ∀ j, α + ‖z j‖ ≤ B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖) :
    ‖jointNeumannResolvent A z B₀ b - jointMatrixResolvent A z‖ ≤
      reciprocalError (jointResolventCondition B₀ r)⁻¹ b / B₀ := by
  let κ := jointResolventCondition B₀ r
  have hκ2 : 2 ≤ κ := le_max_left _ _
  have hκ : 0 < κ := by linarith
  have hκ1 : κ⁻¹ ≤ 1 := (inv_le_one₀ hκ).mpr (by linarith)
  have hi : κ⁻¹ ≤ r / B₀ := by
    have hh := (inv_le_inv₀ hκ (div_pos hB hr)).mpr (le_max_right 2 (B₀ / r))
    simpa only [inv_div] using hh
  obtain ⟨_, hs, _, _⟩ := raw_shifted_encoding H I L A U F α B₀ z henc hB hbound
  have hn : ‖jointNormalizedShift A z B₀‖ ≤ 1 := by
    rw [← hs.encoded]
    exact (compress_norm_le hs.left_isometry hs.right_isometry _).trans
      (unitary_norm_le_one hs.unitary)
  have he := reciprocalMatrixApprox_error_le (jointNormalizedShift A z B₀)
    (inv_pos.mpr hκ) hκ1
    (fun i => (matrixSingularValues_le_spectralNorm _ i).trans hn)
    (fun i _ => hi.trans (jointNormalizedShift_singularValues_lower A z B₀ r hB hr hsep i)) b
  rw [← Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann_eq_reciprocalMatrixApprox,
    jointNormalizedShift_pseudoinverse A z B₀ r hB hr hsep] at he
  have hc : ((B₀⁻¹ : ℝ) : ℂ) * (B₀ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hB.ne', Complex.ofReal_one]
  have ht : jointNeumannResolvent A z B₀ b - jointMatrixResolvent A z =
      ((B₀⁻¹ : ℝ) : ℂ) • (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (jointNormalizedShift A z B₀) b -
        (B₀ : ℂ) • jointMatrixResolvent A z) := by
    rw [smul_sub, smul_smul, hc, one_smul]
    rfl
  rw [ht, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hB)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hB.le)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
