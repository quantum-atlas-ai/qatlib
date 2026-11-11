/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.PolynomialPerturbation
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization

/-!
# Perturbation bounds for encoded polynomial responses

This module transfers coefficient-based polynomial perturbation estimates through Hermitian
dilation and compression. For an approximate block encoding, `encodedBlockPolynomialError`
bounds the change in the response polynomial caused by the normalized encoding error.

The resulting odd and even QSVT statements produce block encodings of the corresponding
polynomial blocks with explicit error, in the singular value transformation framework of
[GilyenSuLowWiebe2019].

## Main statements

* `hermitianDilation_sub_norm`: dilation preserves the norm of a matrix difference.
* `encodedBlock_dilation_polynomial_error`: polynomial responses satisfy the explicit normalized
  error bound.
* `qsvt_odd_encodedBlock_error`: odd QSVT produces the off-diagonal target block with controlled
  error.
* `qsvt_even_left_encodedBlock_error`: even QSVT produces the left diagonal target block with
  controlled error.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section Dilation

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [DecidableEq I] in

/-- The conjugate transpose of the left dilation selector is an isometry. -/
theorem dilationLeft_adjoint_isIsometry :
    IsIsometry (dilationLeft (I := I) (O := O))ᴴ := by
  simp [IsIsometry, dilationLeft, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

omit [DecidableEq O] in

/-- The conjugate transpose of the right dilation selector is an isometry. -/
theorem dilationRight_adjoint_isIsometry :
    IsIsometry (dilationRight (I := I) (O := O))ᴴ := by
  simp [IsIsometry, dilationRight, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

/-- Compression between the left and right dilation embeddings selects the upper-right matrix
block. -/
theorem compress_dilation_selectors12 (M : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    compress dilationLeftᴴ M dilationRightᴴ = M.toBlocks₁₂ := by
  unfold compress
  rw [Matrix.conjTranspose_conjTranspose]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simp [dilationLeft, dilationRight, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

omit [DecidableEq I] in

/-- Compression through the left dilation embedding selects the upper-left matrix block. -/
theorem compress_dilation_selectors11 (M : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    compress dilationLeftᴴ M dilationLeftᴴ = M.toBlocks₁₁ := by
  unfold compress
  rw [Matrix.conjTranspose_conjTranspose]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simp [dilationLeft, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

omit [DecidableEq O] in

/-- Compression through the right dilation embedding selects the lower-right matrix block. -/
theorem compress_dilation_selectors22 (M : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    compress dilationRightᴴ M dilationRightᴴ = M.toBlocks₂₂ := by
  unfold compress
  rw [Matrix.conjTranspose_conjTranspose]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simp [dilationRight, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

/-- The operator norm of the difference of upper-right blocks is at most the norm of the full
matrix difference. -/
theorem dilation_block12_sub_norm_le (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ‖M.toBlocks₁₂ - N.toBlocks₁₂‖ ≤ ‖M - N‖ := by
  simpa only [compress_dilation_selectors12] using
    compress_sub_norm_le (dilationLeft_adjoint_isIsometry (I := I) (O := O))
      (dilationRight_adjoint_isIsometry (I := I) (O := O)) M N

/-- The operator norm of the difference of upper-left blocks is at most the norm of the full
matrix difference. -/
theorem dilation_block11_sub_norm_le (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ‖M.toBlocks₁₁ - N.toBlocks₁₁‖ ≤ ‖M - N‖ := by
  simpa only [compress_dilation_selectors11] using
    compress_sub_norm_le (dilationLeft_adjoint_isIsometry (I := I) (O := O))
      (dilationLeft_adjoint_isIsometry (I := I) (O := O)) M N

/-- The operator norm of the difference of lower-right blocks is at most the norm of the full
matrix difference. -/
theorem dilation_block22_sub_norm_le (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ‖M.toBlocks₂₂ - N.toBlocks₂₂‖ ≤ ‖M - N‖ := by
  simpa only [compress_dilation_selectors22] using
    compress_sub_norm_le (dilationRight_adjoint_isIsometry (I := I) (O := O))
      (dilationRight_adjoint_isIsometry (I := I) (O := O)) M N

/-- Hermitian dilation preserves the operator norm. -/
theorem hermitianDilation_norm (A : Matrix O I ℂ) : ‖hermitianDilation A‖ = ‖A‖ := by
  apply le_antisymm
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    apply (Matrix.toEuclideanCLM (n := O ⊕ I) (𝕜 := ℂ) (hermitianDilation A)).opNorm_le_bound
        (norm_nonneg A)
    intro x
    let xO : EuclideanSpace ℂ O := WithLp.toLp 2 (x.ofLp ∘ Sum.inl)
    let xI : EuclideanSpace ℂ I := WithLp.toLp 2 (x.ofLp ∘ Sum.inr)
    have hx : ‖x‖ ^ 2 = ‖xO‖ ^ 2 + ‖xI‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, xO, xI, Fintype.sum_sum_type]
    have hout : ‖Matrix.toEuclideanCLM (n := O ⊕ I) (𝕜 := ℂ) (hermitianDilation A) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv O ℂ).symm (A *ᵥ xI)‖ ^ 2 +
        ‖(EuclideanSpace.equiv I ℂ).symm (Aᴴ *ᵥ xO)‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
        hermitianDilation, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, xO, xI]
    have hAI := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg xI))).2
      (Matrix.l2_opNorm_mulVec A xI)
    have hAO := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Aᴴ) (norm_nonneg xO))).2
      (Matrix.l2_opNorm_mulVec Aᴴ xO)
    rw [Matrix.l2_opNorm_conjTranspose] at hAO
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg x))).1
    rw [hout, mul_pow]
    calc
      _ ≤ (‖A‖ * ‖xI‖)^2 + (‖A‖ * ‖xO‖)^2 := add_le_add hAI hAO
      _ = ‖A‖^2 * ‖x‖^2 := by rw [hx]; ring
  · have h := compress_norm_le (dilationLeft_adjoint_isIsometry (I := I) (O := O))
      (dilationRight_adjoint_isIsometry (I := I) (O := O)) (hermitianDilation A)
    simpa [compress_dilation_selectors12, hermitianDilation] using h

/-- The norm of the difference of Hermitian dilations equals the norm of the original matrix
difference. -/
theorem hermitianDilation_sub_norm (A B : Matrix O I ℂ) :
    ‖hermitianDilation A - hermitianDilation B‖ = ‖A - B‖ := by
  have he : hermitianDilation A - hermitianDilation B = hermitianDilation (A - B) := by
    ext i j
    cases i <;> cases j <;> simp [hermitianDilation, Matrix.conjTranspose_sub]
  rw [he, hermitianDilation_norm]

/-- For matrices of norm at most a nonnegative `M`, polynomial evaluation on their dilations
differs by at most `‖A - B‖ * coefficientLipschitzBound p M`. -/
theorem dilation_polynomial_perturbation (p : Polynomial ℂ) (A B : Matrix O I ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    ‖aeval (hermitianDilation A) p - aeval (hermitianDilation B) p‖ ≤
      ‖A - B‖ * coefficientLipschitzBound p M := by
  simpa only [hermitianDilation_sub_norm] using
    matrix_polynomial_perturbation p (hermitianDilation A) (hermitianDilation B) hM
      (by simpa only [hermitianDilation_norm] using hA)
      (by simpa only [hermitianDilation_norm] using hB)

end Dilation

/-- The polynomial perturbation budget `(ε / α) * coefficientLipschitzBound p (1 + ε / α)`. -/
noncomputable def encodedBlockPolynomialError (p : Polynomial ℂ) (α ε : ℝ) : ℝ :=
  (ε / α) * coefficientLipschitzBound p (1 + ε / α)

/-- The encoded polynomial error budget is nonnegative for positive scale and nonnegative
encoding error. -/
theorem encodedBlockPolynomialError_nonneg (p : Polynomial ℂ) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 ≤ ε) : 0 ≤ encodedBlockPolynomialError p α ε := by
  have hδ := div_nonneg hε hα.le
  exact mul_nonneg hδ (coefficientLipschitzBound_nonneg p (by linarith))

section EncodedBlock

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]
  {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
  {α ε : ℝ}

/-- The exact compressed block of a block encoding possesses a projected unitary encoding using
the same unitary and frames. -/
theorem decodedBlock_projectedEncoding (h : BlockEncoding A U L R α ε) :
    ProjectedUnitaryEncoding (compress L U R) U L R :=
  ⟨h.unitary, h.left_isometry, h.right_isometry, rfl⟩

/-- The exact compressed block of a block encoding has operator norm at most one. -/
theorem decodedBlock_norm_le_one (h : BlockEncoding A U L R α ε) :
    ‖compress L U R‖ ≤ 1 :=
  (compress_norm_le h.left_isometry h.right_isometry U).trans (unitary_norm_le_one h.unitary)

/-- The compressed block differs from the target divided by its scale by at most `ε / α`. -/
theorem encodedBlock_normalized_error (h : BlockEncoding A U L R α ε) :
    ‖(α⁻¹ : ℝ) • A - compress L U R‖ ≤ ε / α := by
  calc
    _ = ‖(α⁻¹ : ℝ) • (A - α • compress L U R)‖ := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ h.normalization_pos.ne', one_smul]
    _ = α⁻¹ * ‖A - α • compress L U R‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h.normalization_pos)]
    _ ≤ α⁻¹ * ε :=
      mul_le_mul_of_nonneg_left h.error_le (inv_nonneg.mpr h.normalization_pos.le)
    _ = ε / α := by ring

/-- The target divided by the encoding scale has operator norm at most `1 + ε / α`. -/
theorem encodedBlock_normalized_target_norm (h : BlockEncoding A U L R α ε) :
    ‖(α⁻¹ : ℝ) • A‖ ≤ 1 + ε / α := by
  calc
    _ = ‖((α⁻¹ : ℝ) • A - compress L U R) + compress L U R‖ := by rw [sub_add_cancel]
    _ ≤ ‖(α⁻¹ : ℝ) • A - compress L U R‖ + ‖compress L U R‖ := norm_add_le _ _
    _ ≤ ε / α + 1 := add_le_add (encodedBlock_normalized_error h) (decodedBlock_norm_le_one h)
    _ = _ := add_comm _ _

/-- Polynomial evaluation on the normalized target dilation and the compressed-block dilation
differs by at most `encodedBlockPolynomialError p α ε`. -/
theorem encodedBlock_dilation_polynomial_error (h : BlockEncoding A U L R α ε)
    (p : Polynomial ℂ) :
    ‖aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) p -
        aeval (hermitianDilation (compress L U R)) p‖ ≤ encodedBlockPolynomialError p α ε := by
  have hδ : 0 ≤ ε / α := div_nonneg h.error_nonneg h.normalization_pos.le
  have hM : 0 ≤ 1 + ε / α := by linarith
  have hB : ‖compress L U R‖ ≤ 1 + ε / α :=
    (decodedBlock_norm_le_one h).trans (by linarith)
  exact (dilation_polynomial_perturbation p _ _ hM
      (encodedBlock_normalized_target_norm h) hB).trans
    (mul_le_mul_of_nonneg_right (encodedBlock_normalized_error h)
      (coefficientLipschitzBound_nonneg p hM))

/-- An odd QSVT sequence with unit phases block-encodes the upper-right polynomial block of the
normalized target dilation at scale one with the encoded polynomial error budget. -/
theorem qsvt_odd_encodedBlock_error (h : BlockEncoding A U L R α ε)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z)
    (hodd : zs.length % 2 = 1) :
    BlockEncoding
      (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs)).toBlocks₁₂
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R 1
      (encodedBlockPolynomialError (responseP base zs) α ε) := by
  have hactual := qsvt_odd_projectedEncoding (decodedBlock_projectedEncoding h) hb zs hzs hodd
  have herr := (dilation_block12_sub_norm_le
    (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs))
    (aeval (hermitianDilation (compress L U R)) (responseP base zs))).trans
      (encodedBlock_dilation_polynomial_error h (responseP base zs))
  simpa only [zero_add] using (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb
    (encodedBlockPolynomialError_nonneg _ h.normalization_pos h.error_nonneg) herr

/-- An even QSVT sequence with unit phases block-encodes the upper-left polynomial block of the
normalized target dilation at scale one with the encoded polynomial error budget. -/
theorem qsvt_even_left_encodedBlock_error (h : BlockEncoding A U L R α ε)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z)
    (heven : zs.length % 2 = 0) :
    BlockEncoding
      (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs)).toBlocks₁₁
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L L 1
      (encodedBlockPolynomialError (responseP base zs) α ε) := by
  have hactual :=
      qsvt_even_left_projectedEncoding (decodedBlock_projectedEncoding h) hb zs hzs heven
  have herr := (dilation_block11_sub_norm_le
    (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs))
    (aeval (hermitianDilation (compress L U R)) (responseP base zs))).trans
      (encodedBlock_dilation_polynomial_error h (responseP base zs))
  simpa only [zero_add] using (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb
    (encodedBlockPolynomialError_nonneg _ h.normalization_pos h.error_nonneg) herr

/-- The even QSVT sequence using the adjoint oracle block-encodes the lower-right polynomial
block of the normalized target dilation at scale one with the encoded polynomial error
budget. -/
theorem qsvt_even_right_encodedBlock_error (h : BlockEncoding A U L R α ε)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z)
    (heven : zs.length % 2 = 0) :
    BlockEncoding
      (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs)).toBlocks₂₂
      (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R R 1
      (encodedBlockPolynomialError (responseP base zs) α ε) := by
  have hactual :=
      qsvt_even_right_projectedEncoding (decodedBlock_projectedEncoding h) hb zs hzs heven
  have herr := (dilation_block22_sub_norm_le
    (aeval (hermitianDilation ((α⁻¹ : ℝ) • A)) (responseP base zs))
    (aeval (hermitianDilation (compress L U R)) (responseP base zs))).trans
      (encodedBlock_dilation_polynomial_error h (responseP base zs))
  simpa only [zero_add] using (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb
    (encodedBlockPolynomialError_nonneg _ h.normalization_pos h.error_nonneg) herr

end EncodedBlock

end Qatlib.Concepts.CoherentSim.CoherentOAA
