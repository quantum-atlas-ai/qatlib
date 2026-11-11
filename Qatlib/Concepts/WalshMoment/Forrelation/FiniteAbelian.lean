/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Normalized Fourier transforms on finite Abelian groups

This module defines the normalized character Fourier matrix, its action on complex-valued
functions, and the inverse action given by the conjugate transpose. Character orthogonality
proves the two matrix inverse identities and packages the transform as a complex linear
equivalence.

The product-group results identify the dual of a product with the product of the duals and show
that the Fourier matrix factors as a Kronecker product. Finite Abelian Fourier transforms in
quantum algorithms are surveyed in [ChildsVanDam2010].

## Key declarations

* `fourierScale`, `fourierMatrix`, `fourier`, and `fourierInv` fix the normalization and
  conjugation convention.
* `sum_char_mul_conj` and `sum_dual_mul_conj` give character orthogonality.
* `fourierEquiv` packages the forward and inverse transforms.
* `prodDualEquiv`, `fourierMatrix_prod`, and `fourier_prod_apply` describe product
  factorization.

## References

* [Childs and van Dam, 2010][ChildsVanDam2010]
-/

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Matrix
open scoped ComplexConjugate Kronecker Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The complex scalar equal to the reciprocal square root of the cardinality of a finite type. -/
noncomputable def fourierScale (G : Type*) [Fintype G] : ℂ :=
  ((Real.sqrt (Fintype.card G) : ℝ) : ℂ)⁻¹

omit [AddCommGroup G] in

/-- Complex conjugation fixes the Fourier normalization scalar. -/
@[simp] theorem conj_fourierScale : conj (fourierScale G) = fourierScale G := by
  simp [fourierScale]

omit [AddCommGroup G] in

/-- The product of the Fourier normalization scalar with itself is the reciprocal of the finite
cardinality. -/
theorem fourierScale_mul_self : fourierScale G * fourierScale G = (Fintype.card G : ℂ)⁻¹ := by
  have hs : (((Real.sqrt (Fintype.card G) : ℝ) : ℂ)) ^ 2 = (Fintype.card G : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card G) : (0 : ℝ) ≤ Fintype.card G)
  simp only [fourierScale, ← pow_two, inv_pow, hs]

/-- For a finite Abelian group, the square of the Fourier normalization scalar multiplied by the
group cardinality equals one. -/
theorem fourierScale_sq_mul_card :
    (fourierScale G * fourierScale G) * (Fintype.card G : ℂ) = 1 := by
  rw [fourierScale_mul_self, inv_mul_cancel₀]
  exact_mod_cast Fintype.card_ne_zero (α := G)

/-- Two additive characters are orthogonal when summed over the group: their product with one
conjugated sums to the group cardinality if they coincide, and to zero otherwise. -/
theorem sum_char_mul_conj (χ η : AddChar G ℂ) :
    (∑ x, χ x * conj (η x)) = if χ = η then (Fintype.card G : ℂ) else 0 := by
  classical
  simpa only [AddChar.sub_apply, AddChar.map_neg_eq_conj, sub_eq_zero] using
    (AddChar.sum_eq_ite (χ - η))

/-- Summing `χ x * conj (χ y)` over all additive characters gives the group cardinality when `x
= y` and zero otherwise. -/
theorem sum_dual_mul_conj (x y : G) :
    (∑ χ : AddChar G ℂ, χ x * conj (χ y)) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  classical
  simpa only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
    add_neg_eq_zero] using (AddChar.sum_apply_eq_ite (x - y))

/-- The normalized Fourier matrix with rows indexed by additive characters and columns by group
elements, whose entry is `fourierScale G * conj (χ x)`. -/
noncomputable def fourierMatrix (G : Type*) [AddCommGroup G] [Fintype G] :
    Matrix (AddChar G ℂ) G ℂ := fun χ x => fourierScale G * conj (χ x)

/-- The normalized Fourier transform of a complex-valued function on a finite Abelian group,
defined by multiplication with `fourierMatrix G`. -/
noncomputable def fourier (ψ : (G → ℂ)) : (AddChar G ℂ → ℂ) :=
  fourierMatrix G *ᵥ ψ

/-- The inverse normalized Fourier transform, defined by multiplying a function on the character
group by the conjugate transpose of `fourierMatrix G`. -/
noncomputable def fourierInv (φ : (AddChar G ℂ → ℂ)) : (G → ℂ) :=
  (fourierMatrix G)ᴴ *ᵥ φ

/-- The Fourier coefficient at `χ` is `fourierScale G` times the sum of `conj (χ x) * ψ x` over
the group. -/
theorem fourier_apply (ψ : (G → ℂ)) (χ : AddChar G ℂ) :
    fourier ψ χ = fourierScale G * ∑ x, conj (χ x) * ψ x := by
  simp only [fourier, fourierMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The inverse Fourier transform at `x` is `fourierScale G` times the sum of `χ x * φ χ` over
the additive characters. -/
theorem fourierInv_apply (φ : (AddChar G ℂ → ℂ)) (x : G) :
    fourierInv φ x = fourierScale G * ∑ χ, χ x * φ χ := by
  simp only [fourierInv, fourierMatrix, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, RCLike.star_def, map_mul, conj_fourierScale, starRingEnd_self_apply,
    Finset.mul_sum, mul_assoc]

/-- The conjugate transpose of the normalized Fourier matrix multiplied by the Fourier matrix is
the identity on group-indexed vectors. -/
theorem fourierMatrix_conjTranspose_mul [DecidableEq G] :
    (fourierMatrix G)ᴴ * fourierMatrix G = (1 : Matrix G G ℂ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMatrix, RCLike.star_def, map_mul,
    conj_fourierScale, starRingEnd_self_apply]
  calc
    (∑ χ : AddChar G ℂ, (fourierScale G * χ x) * (fourierScale G * conj (χ y))) =
        (fourierScale G * fourierScale G) * ∑ χ : AddChar G ℂ, χ x * conj (χ y) := by
      rw [Finset.mul_sum]
      congr 1; funext χ; ring
    _ = (1 : Matrix G G ℂ) x y := by
      rw [sum_dual_mul_conj]
      by_cases h : x = y <;> simp [h, Matrix.one_apply, fourierScale_sq_mul_card]

/-- The normalized Fourier matrix multiplied by its conjugate transpose is the identity on
character-indexed vectors. -/
theorem fourierMatrix_mul_conjTranspose :
    fourierMatrix G * (fourierMatrix G)ᴴ = (1 : Matrix (AddChar G ℂ) (AddChar G ℂ) ℂ) := by
  classical
  ext χ η
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMatrix, RCLike.star_def, map_mul,
    conj_fourierScale, starRingEnd_self_apply]
  calc
    (∑ x : G, (fourierScale G * conj (χ x)) * (fourierScale G * η x)) =
        (fourierScale G * fourierScale G) * ∑ x : G, η x * conj (χ x) := by
      rw [Finset.mul_sum]
      congr 1; funext x; ring
    _ = (1 : Matrix (AddChar G ℂ) (AddChar G ℂ) ℂ) χ η := by
      rw [sum_char_mul_conj]
      by_cases h : χ = η <;> simp [h, eq_comm, Matrix.one_apply, fourierScale_sq_mul_card]

/-- Applying the inverse Fourier transform after the Fourier transform recovers the original
function on the group. -/
@[simp] theorem fourierInv_fourier [DecidableEq G] (ψ : (G → ℂ)) :
    fourierInv (fourier ψ) = ψ := by
  simp only [fourierInv, fourier, Matrix.mulVec_mulVec, fourierMatrix_conjTranspose_mul,
    Matrix.one_mulVec]

/-- Applying the Fourier transform after the inverse transform recovers the original function on
the character group. -/
@[simp] theorem fourier_fourierInv (φ : (AddChar G ℂ → ℂ)) :
    fourier (fourierInv φ) = φ := by
  classical
  simp only [fourierInv, fourier, Matrix.mulVec_mulVec, fourierMatrix_mul_conjTranspose,
    Matrix.one_mulVec]

/-- The complex linear equivalence between functions on a finite Abelian group and functions on
its character group, with forward map `fourier` and inverse `fourierInv`. -/
noncomputable def fourierEquiv [DecidableEq G] : (G → ℂ) ≃ₗ[ℂ] (AddChar G ℂ → ℂ) where
  toFun := fourier
  invFun := fourierInv
  left_inv := fourierInv_fourier
  right_inv := fourier_fourierInv
  map_add' ψ φ := Matrix.mulVec_add _ ψ φ
  map_smul' c ψ := Matrix.mulVec_smul _ c ψ

section Product
variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- The additive equivalence identifying a pair of characters on `G` and `H` with their product
character on `G × H`. Its inverse restricts a character to the two coordinate inclusions. -/
noncomputable def prodDualEquiv :
    (AddChar G ℂ × AddChar H ℂ) ≃+ AddChar (G × H) ℂ where
  toFun p := p.1.compAddMonoidHom (AddMonoidHom.fst G H) +
    p.2.compAddMonoidHom (AddMonoidHom.snd G H)
  invFun χ := (χ.compAddMonoidHom (AddMonoidHom.inl G H),
    χ.compAddMonoidHom (AddMonoidHom.inr G H))
  left_inv p := by
    rcases p with ⟨χ, η⟩
    ext x <;> simp
  right_inv χ := by
    ext p
    simpa using (χ.map_add_eq_mul (p.1, 0) (0, p.2)).symm
  map_add' p q := by
    ext x
    simp [mul_mul_mul_comm]

omit [Fintype G] [Fintype H] in

/-- The product character associated with `(χ, η)` takes the value `χ x * η y` at `(x, y)`. -/
@[simp] theorem prodDualEquiv_apply (χ : AddChar G ℂ) (η : AddChar H ℂ) (x : G) (y : H) :
    prodDualEquiv (χ, η) (x, y) = χ x * η y := rfl

omit [AddCommGroup G] [AddCommGroup H] in

/-- The Fourier normalization scalar of a product of finite types is the product of their
normalization scalars. -/
theorem fourierScale_prod : fourierScale (G × H) = fourierScale G * fourierScale H := by
  simp [fourierScale, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg (Fintype.card G)), mul_comm]

/-- After indexing product-group characters through `prodDualEquiv`, the Fourier matrix on `G ×
H` is the Kronecker product of the Fourier matrices on `G` and `H`. -/
theorem fourierMatrix_prod :
    (fourierMatrix (G × H)).submatrix prodDualEquiv id =
      fourierMatrix G ⊗ₖ fourierMatrix H := by
  ext ⟨χ, η⟩ ⟨x, y⟩
  simp only [Matrix.submatrix_apply, id_eq, Matrix.kronecker_apply, fourierMatrix,
    prodDualEquiv_apply, map_mul, fourierScale_prod]
  ring

/-- The Fourier transform of the product function `ψ x * φ y`, evaluated at a product character,
is the product of the two individual Fourier coefficients. -/
theorem fourier_prod_apply (ψ : G → ℂ) (φ : H → ℂ)
    (χ : AddChar G ℂ) (η : AddChar H ℂ) :
    fourier (fun p : G × H => ψ p.1 * φ p.2) (prodDualEquiv (χ, η)) =
      fourier ψ χ * fourier φ η := by
  simp only [fourier_apply, Fintype.sum_prod_type, prodDualEquiv_apply,
    map_mul, fourierScale_prod, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end Product

end Qatlib.Concepts.WalshMoment.Forrelation
