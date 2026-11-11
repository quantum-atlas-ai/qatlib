/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Products of independent measurement operators

`liftLeft` and `liftRight` extend matrices to separate registers, and `prodState` forms their
product amplitude function. The lifted operators commute, act componentwise on product states,
and give factored Born weights for product measurements. For background, see [Kitaev1995].

## Main statements

* `liftLeft_liftRight_comm`: proves commutation of operators on separate registers.
* `productMeasurement_born_factor`: factors the joint Born weight into the two single-register
  weights.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator

open Qatlib.Foundations.PureStateMath
open Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The extension of a matrix to the left register, acting as the identity on the right
register. -/
def liftLeft (A : Matrix I I ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.of fun (i, j) (i', j') => if j = j' then A i i' else 0

/-- The extension of a matrix to the right register, acting as the identity on the left
register. -/
def liftRight (B : Matrix J J ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.of fun (i, j) (i', j') => if i = i' then B j j' else 0

/-- The product amplitude function of two register states. -/
def prodState (ψ : QState I) (φ : QState J) : QState (I × J) := fun p => ψ p.1 * φ p.2

/-- An entry of the product of the left and right lifts is the product of the corresponding
component matrix entries. -/
theorem liftLeft_mul_liftRight_apply (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (i i' : I) (j j' : J) :
    (liftLeft A * liftRight B : Matrix (I × J) (I × J) ℂ) (i, j) (i', j') =
      A i i' * B j j' := by
  simp only [Matrix.mul_apply, liftLeft, liftRight, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i') h

/-- An entry of the product of the right and left lifts is the product of the corresponding left
and right matrix entries. -/
theorem liftRight_mul_liftLeft_apply (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (i i' : I) (j j' : J) :
    (liftRight B * liftLeft A : Matrix (I × J) (I × J) ℂ) (i, j) (i', j') =
      A i i' * B j j' := by
  simp only [Matrix.mul_apply, liftLeft, liftRight, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j']
    · simp [mul_comm]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j') h
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Matrices acting on separate registers commute, as used for product measurements in [Kitaev,
Lemma 8][Kitaev1995]. -/
theorem liftLeft_liftRight_comm (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    liftLeft A * liftRight B = liftRight B * liftLeft A := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [liftLeft_mul_liftRight_apply, liftRight_mul_liftLeft_apply]

/-- Applying the product of the lifted matrices to a product state gives the product of the
separately transformed states. -/
theorem applyGate_liftLeft_mul_liftRight (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (ψ : QState I) (φ : QState J) :
    ApplyGate (liftLeft A * liftRight B) (prodState ψ φ) =
      prodState (ApplyGate A ψ) (ApplyGate B φ) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [ApplyGate, prodState, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [liftLeft_mul_liftRight_apply]
  trans ∑ i' : I, ∑ j' : J, (A i i' * ψ i') * (B j j' * φ j')
  · apply Finset.sum_congr rfl
    intro i' _
    apply Finset.sum_congr rfl
    intro j' _
    ring
  · rw [← Finset.sum_mul_sum]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in

/-- The Born weight of a product amplitude function factors into the component Born weights. -/
theorem bornProb_prodState (ψ : QState I) (φ : QState J) (x : I) (y : J) :
    BornProb (prodState ψ φ) (x, y) = BornProb ψ x * BornProb φ y := by
  simp only [BornProb, prodState, norm_mul, mul_pow]

/-- For a product input state, the joint Born weight after the lifted operations equals the
product of the individual transformed Born weights, as in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem productMeasurement_born_factor (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (ψ : QState I) (φ : QState J) (x : I) (y : J) :
    BornProb (ApplyGate (liftLeft A * liftRight B) (prodState ψ φ)) (x, y) =
      BornProb (ApplyGate A ψ) x * BornProb (ApplyGate B φ) y := by
  rw [applyGate_liftLeft_mul_liftRight, bornProb_prodState]

/-- Swapping the order of the left and right lifted operations preserves their action on any
joint state. -/
theorem applyGate_liftLeft_liftRight_swap (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (ρ : QState (I × J)) :
    ApplyGate (liftLeft A * liftRight B) ρ =
      ApplyGate (liftRight B * liftLeft A) ρ := by
  rw [liftLeft_liftRight_comm]

end Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
