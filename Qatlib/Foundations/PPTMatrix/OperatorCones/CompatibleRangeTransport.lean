/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.PPTSubtraction
public import Qatlib.Foundations.PPTMatrix.OperatorCones.TensorMaps

@[expose] public section




/-!
# Transport of compatible ranges under local embeddings

An injective system filter represented by K, with an explicit left inverse L,
transports compatible product ranges through the actual congruence I tensor K.
The witnesses use the adjoint of I tensor L; no surjectivity of K is assumed.
Thus the statement covers both invertible normalization and support embeddings.
-/

open Matrix
open scoped Kronecker

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n p : Type*} [Fintype κ] [DecidableEq κ]
  [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

omit [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- Reference partial transposition commutes with every system linear map. -/
theorem partialTransposeRef_refMap_comm
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    partialTransposeRef (refMap κ Φ X) = refMap κ Φ (partialTransposeRef X) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- The same identity for a literal local congruence. -/
theorem partialTransposeRef_sysConj (K : Matrix p n ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    partialTransposeRef (((1 : Matrix κ κ ℂ) ⊗ₖ K) * X *
      ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ) =
        ((1 : Matrix κ κ ℂ) ⊗ₖ K) * partialTransposeRef X *
          ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ := by
  rw [← refMap_congruenceMap, partialTransposeRef_refMap_comm, refMap_congruenceMap]

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- A local system matrix acts on precisely the second product-vector factor. -/
theorem one_kronecker_mulVec_prodVec (K : Matrix p n ℂ) (a : κ → ℂ) (b : n → ℂ) :
    ((1 : Matrix κ κ ℂ) ⊗ₖ K) *ᵥ prodVec a b = prodVec a (K *ᵥ b) := by
  ext ⟨i, j⟩
  simp [Matrix.mulVec, dotProduct, prodVec, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Finset.mul_sum,
    mul_left_comm, mul_comm]

omit [DecidableEq p] in
/-- An explicit left inverse preserves a compatible nonzero product direction
under local congruence, including rectangular support embeddings. -/
theorem HasCompatibleProductRanges.sysConj_of_leftInverse
    (K : Matrix p n ℂ) (L : Matrix n p ℂ) (hLK : L * K = 1)
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : HasCompatibleProductRanges X) :
    HasCompatibleProductRanges (((1 : Matrix κ κ ℂ) ⊗ₖ K) * X *
      ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ) := by
  let J : Matrix (κ × p) (κ × n) ℂ := (1 : Matrix κ κ ℂ) ⊗ₖ K
  let H : Matrix (κ × n) (κ × p) ℂ := (1 : Matrix κ κ ℂ) ⊗ₖ L
  have hHJ : H * J = 1 := by
    dsimp [H, J]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hLK, Matrix.one_kronecker_one]
  have hJH : Jᴴ * Hᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hHJ
  obtain ⟨a, b, w, z, hab, hw, hz⟩ := hX
  have hprod : J *ᵥ prodVec a b = prodVec a (K *ᵥ b) := one_kronecker_mulVec_prodVec K a b
  have hprodΓ : J *ᵥ prodVec (star a) b = prodVec (star a) (K *ᵥ b) :=
    one_kronecker_mulVec_prodVec K (star a) b
  refine ⟨a, K *ᵥ b, Hᴴ *ᵥ w, Hᴴ *ᵥ z, ?_, ?_, ?_⟩
  · intro hzero
    apply hab
    have h := congrArg (fun v => H *ᵥ v) (hprod.trans hzero)
    simpa only [Matrix.mulVec_mulVec, hHJ, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  · change (J * X * Jᴴ) *ᵥ (Hᴴ *ᵥ w) = _
    calc
      (J * X * Jᴴ) *ᵥ (Hᴴ *ᵥ w) = J *ᵥ (X *ᵥ ((Jᴴ * Hᴴ) *ᵥ w)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = prodVec a (K *ᵥ b) := by rw [hJH, Matrix.one_mulVec, hw, hprod]
  · rw [partialTransposeRef_sysConj]
    change (J * partialTransposeRef X * Jᴴ) *ᵥ (Hᴴ *ᵥ z) = _
    calc
      (J * partialTransposeRef X * Jᴴ) *ᵥ (Hᴴ *ᵥ z) =
          J *ᵥ (partialTransposeRef X *ᵥ ((Jᴴ * Hᴴ) *ᵥ z)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = prodVec (star a) (K *ᵥ b) := by rw [hJH, Matrix.one_mulVec, hz, hprodΓ]

end Qatlib.Foundations.PPTMatrix.OperatorCones
