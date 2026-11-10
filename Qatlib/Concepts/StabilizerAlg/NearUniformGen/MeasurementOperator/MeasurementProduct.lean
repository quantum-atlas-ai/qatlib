/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator

open Qatlib.Foundations.PureStateMath
open Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def liftLeft (A : Matrix I I ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.of fun (i, j) (i', j') => if j = j' then A i i' else 0

def liftRight (B : Matrix J J ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.of fun (i, j) (i', j') => if i = i' then B j j' else 0

def prodState (ψ : QState I) (φ : QState J) : QState (I × J) := fun p => ψ p.1 * φ p.2

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

theorem liftLeft_liftRight_comm (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    liftLeft A * liftRight B = liftRight B * liftLeft A := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [liftLeft_mul_liftRight_apply, liftRight_mul_liftLeft_apply]

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

theorem bornProb_prodState (ψ : QState I) (φ : QState J) (x : I) (y : J) :
    BornProb (prodState ψ φ) (x, y) = BornProb ψ x * BornProb φ y := by
  simp only [BornProb, prodState, norm_mul, mul_pow]

theorem productMeasurement_born_factor (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (ψ : QState I) (φ : QState J) (x : I) (y : J) :
    BornProb (ApplyGate (liftLeft A * liftRight B) (prodState ψ φ)) (x, y) =
      BornProb (ApplyGate A ψ) x * BornProb (ApplyGate B φ) y := by
  rw [applyGate_liftLeft_mul_liftRight, bornProb_prodState]

theorem applyGate_liftLeft_liftRight_swap (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (ρ : QState (I × J)) :
    ApplyGate (liftLeft A * liftRight B) ρ =
      ApplyGate (liftRight B * liftLeft A) ρ := by
  rw [liftLeft_liftRight_comm]

end Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
