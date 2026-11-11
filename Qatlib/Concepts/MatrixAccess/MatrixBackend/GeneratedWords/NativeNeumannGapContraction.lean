/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannStability
import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SpectralSketch.NearIsometry
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

/-! Singular-gap estimates for actual and ideal left defects. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A singular gap on a square matrix also bounds its adjoint from below.
The proof uses the actual pseudoinverse, including in empty dimension. -/
theorem adjoint_singular_gap (S : Matrix I I ℂ) (a : ℝ)
    (ha : 0 < a)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i) :
    ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues Sᴴ i := by
  have hpos : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues S i :=
    fun i => ha.trans_le (hgap i)
  have hleft : matrixPseudoinverse S * S = 1 := (nearColumnPolar_full_support S hpos).2.2
  have hright : S * matrixPseudoinverse S = 1 := mul_eq_one_comm.mp hleft
  have hstar : (matrixPseudoinverse S)ᴴ * Sᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hright
  have hn : ‖matrixPseudoinverse S‖ ≤ a⁻¹ :=
    matrixPseudoinverse_norm_le ha (fun i _ => hgap i)
  intro i
  let v := rightSingularBasis Sᴴ i
  have hv : ‖v‖ = 1 := norm_rightSingularBasis Sᴴ i
  have hid : (matrixPseudoinverse S)ᴴ.toEuclideanLin (Sᴴ.toEuclideanLin v) = v := by
    change ((Matrix.toLpLin 2 2 ((matrixPseudoinverse S)ᴴ)) ∘ₗ
      (Matrix.toLpLin 2 2 Sᴴ)) v = v
    rw [← Matrix.toLpLin_mul_same, hstar]
    simp
  have hbound := Matrix.l2_opNorm_mulVec (matrixPseudoinverse S)ᴴ (Sᴴ.toEuclideanLin v)
  change ‖(matrixPseudoinverse S)ᴴ.toEuclideanLin (Sᴴ.toEuclideanLin v)‖ ≤
    ‖(matrixPseudoinverse S)ᴴ‖ * ‖Sᴴ.toEuclideanLin v‖ at hbound
  rw [hid, hv, Matrix.l2_opNorm_conjTranspose] at hbound
  have ht : 1 ≤ a⁻¹ * ‖Sᴴ.toEuclideanLin v‖ := hbound.trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hs : a ≤ ‖Sᴴ.toEuclideanLin v‖ := by
    have hh := mul_le_mul_of_nonneg_left ht ha.le
    simpa [← mul_assoc, mul_inv_cancel₀ ha.ne'] using hh
  simpa only [v, norm_apply_rightSingularBasis] using hs

/-- A contraction with singular gap a has left defect norm at most 1-a². -/
theorem left_defect_norm_of_singular_gap (S : Matrix I I ℂ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hS : ‖S‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i) :
    ‖1-S*Sᴴ‖ ≤ 1-a^2 := by
  have hg := adjoint_singular_gap S a ha hgap
  have hσ (i : Fin (Fintype.card I)) : matrixSingularValues Sᴴ i ≤ 1 := by
    have h := matrixSingularValues_le_spectralNorm Sᴴ i
    rw [Matrix.l2_opNorm_conjTranspose] at h
    exact h.trans hS
  have hgram : S*Sᴴ = spectralDiagonal (rightSingularBasis Sᴴ)
      (fun i => (matrixSingularValues Sᴴ i : ℂ)^2) := by
    have h := eq_spectralDiagonal_of_action (rightSingularBasis Sᴴ) (S*Sᴴ)
      (fun i => (matrixSingularValues Sᴴ i : ℂ)^2)
    apply h
    intro i
    simpa only [Matrix.conjTranspose_conjTranspose] using gram_apply_rightSingularBasis Sᴴ i
  have hdiag : (1 : Matrix I I ℂ) =
      spectralDiagonal (rightSingularBasis Sᴴ) (fun _ => (1 : ℂ)) := by
    simpa using (spectralDiagonal_const (rightSingularBasis Sᴴ) (1 : ℂ)).symm
  rw [hdiag, hgram, spectralDiagonal_sub]
  apply spectralDiagonal_norm_le _ _ (by nlinarith [sq_nonneg a])
  intro i
  rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · have hh := hg i
    have hh' := hσ i
    nlinarith [sq_nonneg (matrixSingularValues Sᴴ i - a)]
  · have hh := hg i
    have hh' := hσ i
    nlinarith

/-- Actual left defect under perturbation; no invertibility of X is assumed. -/
theorem left_defect_norm_of_singular_gap_perturbed (X S : Matrix I I ℂ) (a δ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i)
    (hδ : ‖X-S‖ ≤ δ) :
    ‖1-X*Xᴴ‖ ≤ 1-a^2+2*δ := by
  have hid : (1-X*Xᴴ) = (1-S*Sᴴ) + ((1-X*Xᴴ)-(1-S*Sᴴ)) := by abel
  have hdiff : ‖(1-X*Xᴴ)-(1-S*Sᴴ)‖ ≤ 2*δ := by
    have he : (1-X*Xᴴ)-(1-S*Sᴴ) = -(X*Xᴴ-S*Sᴴ) := by noncomm_ring
    rw [he, norm_neg]
    have h := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_mul_sub_mul_le X Xᴴ S Sᴴ
    have hx : ‖Xᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hX
    have hd : ‖Xᴴ-Sᴴ‖ = ‖X-S‖ := by
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    rw [hd] at h
    have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg (X-S))
    have hs := mul_le_mul_of_nonneg_right hS (norm_nonneg (X-S))
    linarith
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    (left_defect_norm_of_singular_gap S a ha ha1 hS hgap) hdiff)

/-- A quarter-gap perturbation gives both defects a common radius below one. -/
theorem left_defects_common_gap (X S : Matrix I I ℂ) (a δ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i)
    (hδ : ‖X-S‖ ≤ δ) (hsmall : δ ≤ a^2/4) :
    ‖1-X*Xᴴ‖ ≤ 1-a^2/2 ∧ ‖1-S*Sᴴ‖ ≤ 1-a^2/2 ∧
      0 ≤ 1-a^2/2 ∧ 1-a^2/2 < 1 := by
  have hx := left_defect_norm_of_singular_gap_perturbed X S a δ ha ha1 hX hS hgap hδ
  have hs := left_defect_norm_of_singular_gap S a ha ha1 hS hgap
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (1-a)]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
