/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.CompatibleRangeTransport
public import Qatlib.Foundations.PPTMatrix.OperatorCones.QubitBlocks
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section




/-!
# Invertible normalization of the leading qubit block

A full-rank positive leading block is normalized to the identity by its actual
pseudoinverse square root. Its positive square root is an explicit inverse,
so compatible product ranges transport back to the original PPT matrix.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- Literal block formula for a rectangular local system congruence. -/
theorem qubitBlocks_sysConj (K : Matrix p n ℂ) (A B C D : Matrix n n ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * qubitBlocks A B C D *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ =
        qubitBlocks (K * A * Kᴴ) (K * B * Kᴴ) (K * C * Kᴴ) (K * D * Kᴴ) := by
  rw [← refMap_congruenceMap, refMap_qubitBlocks]
  rfl

omit [Fintype p] [DecidableEq p] in
/-- The pseudoinverse of the identity is the identity, including empty indices. -/
theorem pinv_one_matrix : pinv (1 : Matrix n n ℂ) = 1 := by
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    mul_pinv_mul (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)

omit [Fintype p] [DecidableEq p] in
/-- For a full-rank Hermitian matrix, its support projection is the identity. -/
theorem mul_pinv_eq_one_of_rank_eq_card (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (hrank : A.rank = Fintype.card n) : A * pinv A = 1 := by
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_pi]
    exact hrank
  have hsurj : Function.Surjective A.mulVec :=
    LinearMap.range_eq_top.mp hrange
  have hfun (z : n → ℂ) : (A * pinv A) *ᵥ z = (1 : Matrix n n ℂ) *ᵥ z := by
    obtain ⟨w, rfl⟩ := hsurj z
    rw [Matrix.mulVec_mulVec, mul_pinv_mul hA, Matrix.one_mulVec]
  ext i j
  have h := congrFun (hfun (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

/-- The actual positive square root and inverse square root are mutual inverses
when the positive matrix has full rank. -/
theorem sqrt_inverse_pair_of_full_rank (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (hrank : A.rank = Fintype.card n) :
    pinvSqrt A * psqrt A = 1 ∧ psqrt A * pinvSqrt A = 1 := by
  have h := mul_pinv_eq_one_of_rank_eq_card A hA.isHermitian hrank
  exact ⟨(pinvSqrt_mul_psqrt hA).trans h, (psqrt_mul_pinvSqrt hA).trans h⟩

/-- Congruence by the inverse square root makes the leading block exactly I. -/
theorem pinvSqrt_normalizes_full_rank (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (hrank : A.rank = Fintype.card n) :
    pinvSqrt A * A * (pinvSqrt A)ᴴ = 1 := by
  obtain ⟨hGK, hKG⟩ := sqrt_inverse_pair_of_full_rank A hA hrank
  rw [(isHermitian_pinvSqrt hA).eq]
  calc
    pinvSqrt A * A * pinvSqrt A = pinvSqrt A * (psqrt A * psqrt A) * pinvSqrt A :=
      congrArg (fun M => pinvSqrt A * M * pinvSqrt A) (psqrt_mul_psqrt hA).symm
    _ =
        (pinvSqrt A * psqrt A) * (psqrt A * pinvSqrt A) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hGK, hKG, Matrix.one_mul]

/-- Normalized positivity and PPT give the two actual positive Schur residuals. -/
theorem normalized_schur_posSemidef (B C : Matrix n n ℂ)
    (hX : (qubitBlocks 1 B Bᴴ C).PosSemidef)
    (hΓ : (partialTransposeRef (qubitBlocks 1 B Bᴴ C)).PosSemidef) :
    (C - Bᴴ * B).PosSemidef ∧ (C - B * Bᴴ).PosSemidef := by
  have hR := (posSemidef_fromBlocks_pinv' (posSemidef_qubitBlocks_iff.mp hX)).2.2
  have hΓ' : (qubitBlocks 1 Bᴴ (Bᴴ)ᴴ C).PosSemidef := by
    simpa only [partialTransposeRef_qubitBlocks, Matrix.conjTranspose_conjTranspose] using hΓ
  have hS := (posSemidef_fromBlocks_pinv' (posSemidef_qubitBlocks_iff.mp hΓ')).2.2
  constructor
  · simpa only [pinv_one_matrix, Matrix.mul_one] using hR
  · simpa only [pinv_one_matrix, Matrix.mul_one, Matrix.conjTranspose_conjTranspose] using hS

/-- A normalized compatible-range theorem implies the corresponding theorem
for every PPT block matrix with a full-rank leading block. -/
theorem hasCompatibleProductRanges_of_fullRank_leading_block
    (A B C : Matrix n n ℂ)
    (hX : (qubitBlocks A B Bᴴ C).PosSemidef)
    (hΓ : (partialTransposeRef (qubitBlocks A B Bᴴ C)).PosSemidef)
    (hrank : A.rank = Fintype.card n)
    (hnorm : ∀ B C : Matrix n n ℂ,
      (C - Bᴴ * B).PosSemidef → (C - B * Bᴴ).PosSemidef →
        HasCompatibleProductRanges (qubitBlocks 1 B Bᴴ C)) :
    HasCompatibleProductRanges (qubitBlocks A B Bᴴ C) := by
  have hA := (posSemidef_fromBlocks_pinv' (posSemidef_qubitBlocks_iff.mp hX)).1
  let G := pinvSqrt A
  let K := psqrt A
  let JG : Matrix (Fin 2 × n) (Fin 2 × n) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G
  let JK : Matrix (Fin 2 × n) (Fin 2 × n) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K
  let B' := G * B * Gᴴ
  let C' := G * C * Gᴴ
  have hGA : G * A * Gᴴ = 1 := pinvSqrt_normalizes_full_rank A hA hrank
  have hYeq : JG * qubitBlocks A B Bᴴ C * JGᴴ = qubitBlocks 1 B' B'ᴴ C' := by
    dsimp only [JG, B', C']
    rw [qubitBlocks_sysConj, hGA]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hY : (qubitBlocks 1 B' B'ᴴ C').PosSemidef := by
    rw [← hYeq]
    exact hX.mul_mul_conjTranspose_same JG
  have hΓY : (partialTransposeRef (qubitBlocks 1 B' B'ᴴ C')).PosSemidef := by
    rw [← hYeq]
    change (partialTransposeRef (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G) *
      qubitBlocks A B Bᴴ C * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G)ᴴ)).PosSemidef
    rw [partialTransposeRef_sysConj]
    exact hΓ.mul_mul_conjTranspose_same _
  obtain ⟨hR, hS⟩ := normalized_schur_posSemidef B' C' hY hΓY
  obtain ⟨hGK, hKG⟩ := sqrt_inverse_pair_of_full_rank A hA hrank
  have hYrange := hnorm B' C' hR hS
  have hXrange := hYrange.sysConj_of_leftInverse K G hGK
  have hJKJG : JK * JG = 1 := by
    dsimp only [JK, JG]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (psqrt A * pinvSqrt A) = 1
    rw [hKG, Matrix.one_kronecker_one]
  have hback : JK * (JG * qubitBlocks A B Bᴴ C * JGᴴ) * JKᴴ =
      qubitBlocks A B Bᴴ C := by
    calc
      JK * (JG * qubitBlocks A B Bᴴ C * JGᴴ) * JKᴴ =
          (JK * JG) * qubitBlocks A B Bᴴ C * (JK * JG)ᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = qubitBlocks A B Bᴴ C := by
        rw [hJKJG, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  change HasCompatibleProductRanges (JK * qubitBlocks 1 B' B'ᴴ C' * JKᴴ) at hXrange
  rwa [← hYeq, hback] at hXrange

end Qatlib.Foundations.PPTMatrix.OperatorCones
