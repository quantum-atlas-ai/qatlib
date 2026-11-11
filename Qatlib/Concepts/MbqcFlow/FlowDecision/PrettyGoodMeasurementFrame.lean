/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementData

/-!
# Support identities for pretty-good frames

Proves functional-calculus identities for the reciprocal square root of `ensembleGram W` and
derives the corresponding identities for `prettyGoodFrame W`. In particular, the frame Gram
matrix is the support projection of the original Gram matrix.

The theorem `pretty_good_frame_support_contract` packages the Hermitian projection property of
`F * Fᴴ` and positivity of its complement. The matrix-analysis background is given in
[Bhatia1997].

## Main statements

* `pretty_good_frame_support_contract`: frame, Gram square-root, and support-projection
  identities.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

/-- For a nonnegative real number, its reciprocal square root multiplied by the number equals
its square root. -/
private theorem reciprocal_sqrt_mul_self (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hpos : 0 < Real.sqrt x :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne hx (Ne.symm hzero))
    calc
      (Real.sqrt x)⁻¹ * x = (Real.sqrt x)⁻¹ * (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- For a nonnegative real number, the square root times its reciprocal equals zero at zero and
one otherwise. -/
private theorem sqrt_mul_reciprocal_eq_support (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1 := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hpos : 0 < Real.sqrt x :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne hx (Ne.symm hzero))
    rw [if_neg hzero, mul_inv_cancel₀ hpos.ne']

variable {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}

/-- The reciprocal square root of the ensemble Gram matrix times the Gram matrix equals its
square root. -/
private theorem ensemble_inv_sqrt_mul_gram (W : Matrix (Fin D) I ℂ) :
    (ensembleGramInvSqrt W).mat * (ensembleGram W).mat =
      (ensembleGram W).sqrt.mat := by
  calc
    (ensembleGramInvSqrt W).mat * (ensembleGram W).mat =
        ((ensembleGram W).cfc
          (fun x : ℝ => (Real.sqrt x)⁻¹ * x)).mat := by
      rw [HermitianMat.mat_cfc_mul_apply, HermitianMat.cfc_id']
      rfl
    _ = (ensembleGram W).sqrt.mat := by
      apply congrArg HermitianMat.mat
      exact HermitianMat.cfc_congr_of_nonneg (ensembleGram_nonneg W)
        (fun x hx => reciprocal_sqrt_mul_self x hx)

/-- The Gram square root times its reciprocal square root equals the Gram support projection. -/
private theorem ensemble_sqrt_mul_inv_sqrt (W : Matrix (Fin D) I ℂ) :
    (ensembleGram W).sqrt.mat * (ensembleGramInvSqrt W).mat =
      (ensembleGram W).supportProj.mat := by
  calc
    (ensembleGram W).sqrt.mat * (ensembleGramInvSqrt W).mat =
        ((ensembleGram W).cfc
          (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹)).mat := by
      rw [HermitianMat.mat_cfc_mul_apply]
      rfl
    _ = (ensembleGram W).supportProj.mat := by
      rw [HermitianMat.supportProj_eq_cfc]
      apply congrArg HermitianMat.mat
      exact HermitianMat.cfc_congr_of_nonneg (ensembleGram_nonneg W)
        (fun x hx => sqrt_mul_reciprocal_eq_support x hx)

/-- Multiplication by the Gram support projection leaves the reciprocal Gram square root
unchanged. -/
private theorem ensemble_inv_sqrt_mul_support (W : Matrix (Fin D) I ℂ) :
    (ensembleGramInvSqrt W).mat * (ensembleGram W).supportProj.mat =
      (ensembleGramInvSqrt W).mat := by
  calc
    (ensembleGramInvSqrt W).mat * (ensembleGram W).supportProj.mat =
        ((ensembleGram W).cfc (fun x : ℝ =>
          (Real.sqrt x)⁻¹ * (if x = 0 then 0 else 1))).mat := by
      rw [HermitianMat.mat_cfc_mul_apply, ← HermitianMat.supportProj_eq_cfc]
      rfl
    _ = (ensembleGramInvSqrt W).mat := by
      apply congrArg HermitianMat.mat
      apply HermitianMat.cfc_congr_of_nonneg (ensembleGram_nonneg W)
      intro x _
      by_cases hzero : x = 0 <;> simp [hzero]

/-- The adjoint of the pretty-good frame times `W` equals the Gram square root. -/
private theorem pretty_good_frame_adjoint_original (W : Matrix (Fin D) I ℂ) :
    (prettyGoodFrame W)ᴴ * W = (ensembleGram W).sqrt.mat := by
  calc
    (prettyGoodFrame W)ᴴ * W =
        (ensembleGramInvSqrt W).mat * (ensembleGram W).mat := by
      rw [prettyGoodFrame, Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat]
      change (ensembleGramInvSqrt W).mat * Wᴴ * W =
        (ensembleGramInvSqrt W).mat * (Wᴴ * W)
      exact Matrix.mul_assoc _ _ _
    _ = (ensembleGram W).sqrt.mat := ensemble_inv_sqrt_mul_gram W

/-- The Gram matrix of the pretty-good frame equals the support projection of the original Gram
matrix. -/
private theorem pretty_good_frame_adjoint_frame (W : Matrix (Fin D) I ℂ) :
    (prettyGoodFrame W)ᴴ * prettyGoodFrame W =
      (ensembleGram W).supportProj.mat := by
  calc
    (prettyGoodFrame W)ᴴ * prettyGoodFrame W =
        ((ensembleGramInvSqrt W).mat * (ensembleGram W).mat) *
          (ensembleGramInvSqrt W).mat := by
      simp only [prettyGoodFrame, Matrix.conjTranspose_mul,
        HermitianMat.conjTranspose_mat]
      change (ensembleGramInvSqrt W).mat * Wᴴ *
          (W * (ensembleGramInvSqrt W).mat) =
        ((ensembleGramInvSqrt W).mat * (Wᴴ * W)) *
          (ensembleGramInvSqrt W).mat
      simp only [Matrix.mul_assoc]
    _ = (ensembleGram W).sqrt.mat * (ensembleGramInvSqrt W).mat := by
      rw [ensemble_inv_sqrt_mul_gram]
    _ = (ensembleGram W).supportProj.mat := ensemble_sqrt_mul_inv_sqrt W

/-- The pretty-good frame is unchanged by right multiplication by the Gram support projection. -/
private theorem pretty_good_frame_mul_support (W : Matrix (Fin D) I ℂ) :
    prettyGoodFrame W * (ensembleGram W).supportProj.mat = prettyGoodFrame W := by
  rw [prettyGoodFrame, Matrix.mul_assoc, ensemble_inv_sqrt_mul_support]

/-- For the pretty-good frame `F`, proves the Gram square-root and support identities, Hermitian
idempotence of `F * Fᴴ`, and positive semidefiniteness of its complement. -/
theorem pretty_good_frame_support_contract
    (I : Type) [Fintype I] [DecidableEq I] (D : ℕ) (W : Matrix (Fin D) I ℂ) :
    let F := prettyGoodFrame W
    Fᴴ * W = (ensembleGram W).sqrt.mat ∧
      Fᴴ * F = (ensembleGram W).supportProj.mat ∧
      (F * Fᴴ).IsHermitian ∧ (F * Fᴴ) * (F * Fᴴ) = F * Fᴴ ∧
      (1 - F * Fᴴ).PosSemidef := by
  let F := prettyGoodFrame W
  have hgram : Fᴴ * F = (ensembleGram W).supportProj.mat :=
    pretty_good_frame_adjoint_frame W
  have hsupport : F * (ensembleGram W).supportProj.mat = F :=
    pretty_good_frame_mul_support W
  have hherm : (F * Fᴴ).IsHermitian :=
    (Matrix.posSemidef_self_mul_conjTranspose F).1
  have hidem : (F * Fᴴ) * (F * Fᴴ) = F * Fᴴ := by
    calc
      (F * Fᴴ) * (F * Fᴴ) = (F * (Fᴴ * F)) * Fᴴ := by
        simp only [Matrix.mul_assoc]
      _ = (F * (ensembleGram W).supportProj.mat) * Fᴴ := by rw [hgram]
      _ = F * Fᴴ := by rw [hsupport]
  have hfactor : (1 - F * Fᴴ)ᴴ * (1 - F * Fᴴ) = 1 - F * Fᴴ := by
    have hstar : (F * Fᴴ)ᴴ = F * Fᴴ := hherm
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hidem, sub_self, sub_zero]
  have hreject : (1 - F * Fᴴ).PosSemidef := by
    rw [← hfactor]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  exact ⟨pretty_good_frame_adjoint_original W, hgram, hherm, hidem, hreject⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
