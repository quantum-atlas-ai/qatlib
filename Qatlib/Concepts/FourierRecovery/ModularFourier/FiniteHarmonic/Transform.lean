/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Quantum-normalized Fourier transform on a finite abelian group

The input basis is `G`, the output basis is Mathlib's `AddChar G ℂ`.
`fourierMatrix G χ x = (sqrt(card G))⁻¹ * conj(χ x)`; no identification
of a group with its dual is implicit. Orthogonality and dual cardinality are
transported from the pinned Mathlib character theory, not supplied by callers.
The companion `FiniteAbelianFourierState` module connects this rectangular matrix
to the existing `Inner`, `Normalized`, tensor and Born semantics. Square circuit
gates require an explicit known output labelling.
This is exact finite-dimensional semantics, not efficient Fourier synthesis.
-/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

open Matrix
open scoped ComplexConjugate Kronecker Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Quantum, rather than probability-average, normalization. -/
noncomputable def fourierScale (G : Type*) [Fintype G] : ℂ :=
  ((Real.sqrt (Fintype.card G) : ℝ) : ℂ)⁻¹

omit [AddCommGroup G] in
/-- The quantum Fourier normalization `fourierScale G` is real, hence invariant under complex conjugation. -/
@[simp] theorem conj_fourierScale : conj (fourierScale G) = fourierScale G := by
  simp [fourierScale]

omit [AddCommGroup G] in
/-- The square of the quantum normalizer is the inverse group order. -/
theorem fourierScale_mul_self : fourierScale G * fourierScale G = (Fintype.card G : ℂ)⁻¹ := by
  have hs : (((Real.sqrt (Fintype.card G) : ℝ) : ℂ)) ^ 2 = (Fintype.card G : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card G) : (0 : ℝ) ≤ Fintype.card G)
  simp only [fourierScale, ← pow_two, inv_pow, hs]

/-- The squared quantum normalization, multiplied by the group order, is one. -/
theorem fourierScale_sq_mul_card :
    (fourierScale G * fourierScale G) * (Fintype.card G : ℂ) = 1 := by
  rw [fourierScale_mul_self, inv_mul_cancel₀]
  exact_mod_cast Fintype.card_ne_zero (α := G)

/-- Orthogonality as a counting sum, with the sign used by the quantum transform. -/
theorem sum_char_mul_conj (χ η : AddChar G ℂ) :
    (∑ x, χ x * conj (η x)) = if χ = η then (Fintype.card G : ℂ) else 0 := by
  classical
  simpa only [AddChar.sub_apply, AddChar.map_neg_eq_conj, sub_eq_zero] using
    (AddChar.sum_eq_ite (χ - η))

/-- Dual orthogonality, without choosing an isomorphism from `G` to its dual. -/
theorem sum_dual_mul_conj (x y : G) :
    (∑ χ : AddChar G ℂ, χ x * conj (χ y)) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  classical
  simpa only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
    add_neg_eq_zero] using (AddChar.sum_apply_eq_ite (x - y))

/-- Fourier matrix with genuinely different input and output basis types. -/
noncomputable def fourierMatrix (G : Type*) [AddCommGroup G] [Fintype G] :
    Matrix (AddChar G ℂ) G ℂ := fun χ x => fourierScale G * conj (χ x)

/-- The output is a state on the dual group, not silently a state on `G`. -/
noncomputable def fourier (ψ : (G → ℂ)) : (AddChar G ℂ → ℂ) :=
  fourierMatrix G *ᵥ ψ

/-- The adjoint transform, returning to the original basis. -/
noncomputable def fourierInv (φ : (AddChar G ℂ → ℂ)) : (G → ℂ) :=
  (fourierMatrix G)ᴴ *ᵥ φ

/-- Explicit amplitude formula, including the conjugation convention. -/
theorem fourier_apply (ψ : (G → ℂ)) (χ : AddChar G ℂ) :
    fourier ψ χ = fourierScale G * ∑ x, conj (χ x) * ψ x := by
  simp only [fourier, fourierMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Explicit inverse amplitude formula. -/
theorem fourierInv_apply (φ : (AddChar G ℂ → ℂ)) (x : G) :
    fourierInv φ x = fourierScale G * ∑ χ, χ x * φ χ := by
  simp only [fourierInv, fourierMatrix, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, RCLike.star_def, map_mul, conj_fourierScale, starRingEnd_self_apply,
    Finset.mul_sum, mul_assoc]

/-- Column orthonormality: the adjoint is a left inverse on `G`. -/
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

/-- Row orthonormality: no output character is lost. -/
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

/-- The inverse Fourier transform inverts the Fourier transform on functions on `G`. -/
@[simp] theorem fourierInv_fourier [DecidableEq G] (ψ : (G → ℂ)) :
    fourierInv (fourier ψ) = ψ := by
  simp only [fourierInv, fourier, Matrix.mulVec_mulVec, fourierMatrix_conjTranspose_mul,
    Matrix.one_mulVec]

/-- The Fourier transform inverts the inverse Fourier transform on functions on the dual. -/
@[simp] theorem fourier_fourierInv (φ : (AddChar G ℂ → ℂ)) :
    fourier (fourierInv φ) = φ := by
  classical
  simp only [fourierInv, fourier, Matrix.mulVec_mulVec, fourierMatrix_mul_conjTranspose,
    Matrix.one_mulVec]

/-- The state map as a Mathlib linear equivalence, with the proved adjoint inverse. -/
noncomputable def fourierEquiv [DecidableEq G] : (G → ℂ) ≃ₗ[ℂ] (AddChar G ℂ → ℂ) where
  toFun := fourier
  invFun := fourierInv
  left_inv := fourierInv_fourier
  right_inv := fourier_fourierInv
  map_add' ψ φ := Matrix.mulVec_add _ ψ φ
  map_smul' c ψ := Matrix.mulVec_smul _ c ψ

end Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
