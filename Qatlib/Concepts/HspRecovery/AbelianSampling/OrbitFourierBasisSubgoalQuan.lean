/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasisSubgoalStat

/-!
# Orthogonality and translation eigenvalues of Fourier vectors

This module proves orthonormality of the normalized character vectors and their eigenvector
property under translation. It also expresses `Ket 0` as their equal amplitude sum, assembling
these facts in `orbitFourierBasisSubgoal` for abelian stabilizer sampling. [Kitaev1995]

## Main statements

* `orbitFourierBasisSubgoal`: proves orthonormality, the eigenvalue `χ (-g₀)`, and the expansion
  of `Ket 0`.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Matrix
open scoped Classical BigOperators

variable (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in

/-- The complex conjugate of a character value on a finite abelian group equals its
multiplicative inverse. -/
private theorem conj_addChar_apply (χ : AddChar E ℂ) (g : E) :
    (starRingEnd ℂ) (χ g) = (χ g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply, one_pow,
    Complex.ofReal_one]

omit [Fintype E] [DecidableEq E] in

/-- Evaluating an additive character at `-g` gives the inverse of its value at `g`. -/
private theorem addChar_apply_neg (χ : AddChar E ℂ) (g : E) :
    χ (-g) = (χ g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

omit [DecidableEq E] in

/-- The product of the conjugate of `χ g` with `η g` is the value of the character `η * χ⁻¹` at
`g`. -/
private theorem conj_mul_eq_mul_inv_apply (χ η : AddChar E ℂ) (g : E) :
    (starRingEnd ℂ) (χ g) * (η g) = (η * χ⁻¹) g := by
  rw [AddChar.mul_apply, AddChar.inv_apply, conj_addChar_apply E χ g,
    addChar_apply_neg E χ g, mul_comm]

omit [DecidableEq E] in

/-- The sum of conjugate products of two complex additive characters is the group cardinality
when they coincide and zero otherwise. -/
private theorem sum_conj_mul (χ η : AddChar E ℂ) :
    (∑ g : E, (starRingEnd ℂ) (χ g) * (η g)) =
      if χ = η then (Fintype.card E : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun g _ => conj_mul_eq_mul_inv_apply E χ η g),
    AddChar.sum_eq_ite]
  by_cases h : χ = η
  · rw [if_pos h]
    subst h
    rw [if_pos ((mul_inv_cancel χ).trans AddChar.one_eq_zero)]
  · rw [if_neg h, if_neg (fun hh =>
      h ((mul_inv_eq_one.mp (hh.trans AddChar.one_eq_zero.symm)).symm))]

omit [DecidableEq E] in

/-- The square of the reciprocal square root of the finite group cardinality, multiplied by that
cardinality, equals one in the complex numbers. -/
private theorem inv_sqrt_sq_mul_card :
    ((↑((Real.sqrt ((Fintype.card E : ℝ)))⁻¹) : ℂ)) ^ 2 * (Fintype.card E : ℂ) = 1 := by
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, inv_pow,
    Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne', Complex.ofReal_one]

/-- Normalized character vectors are orthonormal: their inner product is one for equal
characters and zero otherwise. -/
private theorem orbitFourierVec_inner (χ η : AddChar E ℂ) :
    Inner (orbitFourierVec E χ) (orbitFourierVec E η) = if χ = η then 1 else 0 := by
  rw [inner_apply]
  have hpt : ∀ g : E,
      (starRingEnd ℂ) (orbitFourierVec E χ g) * (orbitFourierVec E η g)
        = ((↑((Real.sqrt ((Fintype.card E : ℝ)))⁻¹) : ℂ)) ^ 2 *
            ((starRingEnd ℂ) (χ g) * (η g)) := by
    intro g
    simp only [orbitFourierVec]
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl (fun g _ => hpt g), ← Finset.mul_sum, sum_conj_mul E χ η]
  by_cases h : χ = η
  · rw [if_pos h, if_pos h]
    exact inv_sqrt_sq_mul_card E
  · rw [if_neg h, if_neg h, mul_zero]

/-- Translation by `g₀` acts on state coordinates by evaluating the original state at `i - g₀`. -/
private theorem orbitRegMatrix_mulVec_apply (g₀ : E) (ψ : QState E) (i : E) :
    ((orbitRegMatrix E g₀) *ᵥ ψ) i = ψ (i - g₀) := by
  simp only [orbitRegMatrix, permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (i - g₀)]
  · rw [if_pos (sub_add_cancel i g₀).symm, one_mul]
  · intro j _ hj
    rw [if_neg (fun hij => hj (sub_eq_iff_eq_add.mpr hij).symm), zero_mul]
  · simp

/-- The Fourier vector for `χ` is an eigenvector of translation by `g₀` with eigenvalue `χ
(-g₀)`. -/
private theorem orbitFourierVec_eigen (g₀ : E) (χ : AddChar E ℂ) :
    ApplyGate (orbitRegMatrix E g₀) (orbitFourierVec E χ)
      = (χ (-g₀)) • orbitFourierVec E χ := by
  funext i
  simp only [ApplyGate, Pi.smul_apply, smul_eq_mul]
  rw [orbitRegMatrix_mulVec_apply E g₀ _ i]
  simp only [orbitFourierVec]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

omit [AddCommGroup E] [Fintype E] [DecidableEq E] in

/-- Real scalar multiplication of a quantum state is pointwise multiplication by the
corresponding complex scalar. -/
private theorem real_smul_qstate_apply (r : ℝ) (f : QState E) (g : E) :
    (r • f) g = (↑r : ℂ) * f g := rfl

/-- The equal amplitude sum of all normalized character vectors, with coefficient `1 / sqrt(card
E)`, equals `Ket 0`. -/
private theorem orbitFourierVec_decomp :
    (∑ χ : AddChar E ℂ,
        ((Real.sqrt ((Fintype.card E : ℝ)))⁻¹ • orbitFourierVec E χ)) = Ket (0 : E) := by
  funext g
  simp only [Finset.sum_apply, real_smul_qstate_apply, orbitFourierVec]
  rw [Finset.sum_congr rfl (fun χ _ => (mul_assoc _ _ _).symm), ← Finset.mul_sum,
    AddChar.sum_apply_eq_ite]
  show _ = Ket (0 : E) g
  rw [ket_apply]
  by_cases h : g = 0
  · rw [if_pos h, if_pos h]
    rw [← pow_two]
    exact inv_sqrt_sq_mul_card E
  · rw [if_neg h, if_neg h, mul_zero]

/-- The normalized character vectors are orthonormal translation eigenvectors with eigenvalue `χ
(-g₀)`, and their equal amplitude sum gives `Ket 0` [Kitaev1995]. -/
theorem orbitFourierBasisSubgoal : OrbitFourierBasisSubgoal := by
  intro E _ _ _
  exact ⟨orbitFourierVec_inner E, orbitFourierVec_eigen E, orbitFourierVec_decomp E⟩

end Qatlib.Concepts.HspRecovery.AbelianSampling
