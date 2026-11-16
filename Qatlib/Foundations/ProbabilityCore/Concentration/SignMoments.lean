/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Exact finite independent-sign moments

The uniform law is the actual full finite Boolean-function space. Off-diagonal
moments cancel by a measure-preserving coordinate flip, rather than being
assumed as a Parseval or independence contract.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators

namespace Qatlib.Foundations.ProbabilityCore.Concentration.SignMoments

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The literal source sign is minus one at true and plus one at false. -/
def rSign (b : Bool) : ℂ := if b then -1 else 1

/-- Complementing a bit negates its real complex sign. -/
theorem signNot (b : Bool) : rSign (!b) = -rSign b := by
  cases b <;> norm_num [rSign]

/-- Every actual Boolean sign has square one. -/
theorem signSquare (b : Bool) : rSign b * rSign b = 1 := by
  cases b <;> norm_num [rSign]

/-- Real Boolean signs are fixed by complex conjugation. -/
theorem signStar (b : Bool) : star (rSign b) = rSign b := by
  cases b <;> simp [rSign]

/-- Flip a single coordinate of the actual full finite sign space. -/
def flipAt (i : I) : (I → Bool) ≃ (I → Bool) where
  toFun f := Function.update f i (!(f i))
  invFun f := Function.update f i (!(f i))
  left_inv f := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]
  right_inv f := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]

/-- Exact pair orthogonality follows from a real coordinate-flip bijection. -/
theorem signPairSum (i j : I) :
    (∑ f : I → Bool, rSign (f i) * rSign (f j)) =
      if i = j then (Fintype.card (I → Bool) : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [signSquare, ite_true]
    simp
  · rw [ite_eq_right hij]
    have hn (f : I → Bool) :
        rSign ((flipAt i) f i) * rSign ((flipAt i) f j) =
          -(rSign (f i) * rSign (f j)) := by
      simp [flipAt, Function.update_of_ne (Ne.symm hij), signNot]
    have hsum : (∑ f : I → Bool, rSign (f i) * rSign (f j)) =
        -(∑ f : I → Bool, rSign (f i) * rSign (f j)) := by
      calc (∑ f : I → Bool, rSign (f i) * rSign (f j)) =
          ∑ f : I → Bool, rSign ((flipAt i) f i) * rSign ((flipAt i) f j) :=
            (Equiv.sum_comp (flipAt i) _).symm
        _ = ∑ f : I → Bool, -(rSign (f i) * rSign (f j)) :=
          Finset.sum_congr rfl (fun f _ => hn f)
        _ = _ := by rw [Finset.sum_neg_distrib]
    have hz : (2 : ℂ) * (∑ f : I → Bool, rSign (f i) * rSign (f j)) = 0 := by
      linear_combination hsum
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The conjugate second moment is derived by expanding actual independent signs. -/
theorem starMoment (v : I → ℂ) :
    (∑ f : I → Bool, star (∑ i, rSign (f i) * v i) *
      (∑ i, rSign (f i) * v i)) =
      (Fintype.card (I → Bool) : ℂ) * ∑ i, star (v i) * v i := by
  calc
    _ = ∑ i, ∑ j, ∑ f : I → Bool,
        (rSign (f i) * rSign (f j)) * (star (v i) * v j) := by
      simp_rw [star_sum, star_mul, signStar, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by
      simp_rw [← Finset.sum_mul, signPairSum]
      simp [Finset.mul_sum]

/-- Exact squared-norm second moment, including the empty coordinate space. -/
theorem normMoment (v : I → ℂ) :
    (∑ f : I → Bool, ‖∑ i, rSign (f i) * v i‖ ^ 2) =
      (Fintype.card (I → Bool) : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  exact starMoment v

/-- Two independent finite sign vectors give the exact matrix second moment. -/
theorem matrixMoment {J : Type*} [Fintype J] [DecidableEq J] (A : I → J → ℂ) :
    (∑ f : J → Bool, ∑ g : I → Bool,
      ‖∑ i, rSign (g i) * (∑ j, A i j * rSign (f j))‖ ^ 2) =
      (Fintype.card (I → Bool) : ℝ) * (Fintype.card (J → Bool) : ℝ) *
        ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp_rw [normMoment, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (i : I) :
      (∑ f : J → Bool, ‖∑ j, A i j * rSign (f j)‖ ^ 2) =
        (Fintype.card (J → Bool) : ℝ) * ∑ j, ‖A i j‖ ^ 2 := by
    simpa only [mul_comm] using normMoment (A i)
  simp_rw [h, ← Finset.mul_sum]
  ring

end Qatlib.Foundations.ProbabilityCore.Concentration.SignMoments
