/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NeumannResolvent
import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA

/-! Dimension-free perturbation of the left-defect Neumann polynomial.
No normality or nonempty-dimensionality hypothesis is required. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable local instance {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The finite construction in `NativeNeumannStability` satisfies `defect_norm_le_one` under the displayed hypotheses. -/
private theorem defect_norm_le_one (X : Matrix I I ℂ) (hX : ‖X‖ ≤ 1) :
    ‖1-X*Xᴴ‖ ≤ 1 := by
  have hp : 0 ≤ X*Xᴴ := (Matrix.posSemidef_self_mul_conjTranspose X).nonneg
  have hn : ‖X*Xᴴ‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
    rw [h]
    nlinarith [norm_nonneg X]
  have hle : X*Xᴴ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (X*Xᴴ) hp).mp hn
  have hd : 0 ≤ 1-X*Xᴴ := sub_nonneg.mpr hle
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1-X*Xᴴ) hd).mpr (sub_le_self _ hp)

/-- The finite construction in `NativeNeumannStability` satisfies `defect_difference_le` under the displayed hypotheses. -/
private theorem defect_difference_le (X S : Matrix I I ℂ)
    (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1) :
    ‖(1-X*Xᴴ)-(1-S*Sᴴ)‖ ≤ 2*‖X-S‖ := by
  have he : (1-X*Xᴴ)-(1-S*Sᴴ) = -(X*Xᴴ-S*Sᴴ) := by noncomm_ring
  rw [he, norm_neg]
  have h := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_mul_sub_mul_le X Xᴴ S Sᴴ
  have hx : ‖Xᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hX
  have hd : ‖Xᴴ-Sᴴ‖ = ‖X-S‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  rw [hd] at h
  have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg (X-S))
  have hn := mul_le_mul_of_nonneg_right hS (norm_nonneg (X-S))
  nlinarith

/-- The actual unnormalized b-term Neumann polynomial is b²-Lipschitz on
contractions, for all finite dimensions including the empty type. -/
theorem leftDefectNeumann_perturbation (X S : Matrix I I ℂ) (b : ℕ)
    (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b-Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b‖ ≤ (b : ℝ)^2 * ‖X-S‖ := by
  let DX : Matrix I I ℂ := 1-X*Xᴴ
  let DS : Matrix I I ℂ := 1-S*Sᴴ
  have hDX : ‖DX‖ ≤ 1 := defect_norm_le_one X hX
  have hDS : ‖DS‖ ≤ 1 := defect_norm_le_one S hS
  have hdiff : ‖DX-DS‖ ≤ 2*‖X-S‖ := defect_difference_le X S hX hS
  have hxadj : ‖Xᴴ-Sᴴ‖ = ‖X-S‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  have hsadj : ‖Sᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hS
  have hterm (k : ℕ) : ‖Xᴴ*DX^k-Sᴴ*DS^k‖ ≤
      (2*(k:ℝ)+1)*‖X-S‖ := by
    have hp := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_pow_le_one DX hDX k
    have hd := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_pow_sub_pow_le DX DS hDX hDS k
    have hm := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_mul_sub_mul_le Xᴴ (DX^k) Sᴴ (DS^k)
    rw [hxadj] at hm
    have hp' := mul_le_mul_of_nonneg_left hp (norm_nonneg (X-S))
    have hd' := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg k)
    have hs' := mul_le_mul_of_nonneg_right hsadj (norm_nonneg (DX^k-DS^k))
    nlinarith
  have hsum : (∑ k ∈ Finset.range b, (2*(k:ℝ)+1)) = (b:ℝ)^2 := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann, Matrix.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range b, ‖Xᴴ*DX^k-Sᴴ*DS^k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range b, (2*(k:ℝ)+1)*‖X-S‖ := by
      exact Finset.sum_le_sum (fun k _ => hterm k)
    _ = _ := by rw [← Finset.sum_mul, hsum]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
