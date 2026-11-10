/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ThermalRate98.MainResults

theorem source_boltzmann_suppression (β E_lo E_hi : ℝ) (hβ : 0 < β) (h : E_lo ≤ E_hi) :
    Real.exp (-(β * E_hi)) ≤ Real.exp (-(β * E_lo)) := by
  apply Real.exp_le_exp.2
  nlinarith

theorem source_boltzmann_relative_suppression (β E₀ E : ℝ) (hβ : 0 < β) (h : E₀ ≤ E) :
    Real.exp (-(β * E)) ≤ Real.exp (-(β * E₀)) :=
  source_boltzmann_suppression β E₀ E hβ h

theorem source_boltzmann_tail_sum {I : Type*} [Fintype I] (β E₀ : ℝ) (hβ : 0 < β)
    (E : I → ℝ) (S : Finset I) (hb : ∀ n ∈ S, E₀ ≤ E n) :
    (∑ n ∈ S, Real.exp (-(β * E n))) ≤
      (S.card : ℝ) * Real.exp (-(β * E₀)) := by
  calc (∑ n ∈ S, Real.exp (-(β * E n)))
      ≤ ∑ _n ∈ S, Real.exp (-(β * E₀)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact source_boltzmann_suppression β E₀ (E n) hβ (hb n hn)
    _ = (S.card : ℝ) * Real.exp (-(β * E₀)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

theorem source_active_set_truncation {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → I → ℂ) (S : Finset I)
    (h : ∀ n m, n ∉ S ∨ m ∉ S → f n m = 0) :
    (∑ n, ∑ m, f n m) = ∑ n ∈ S, ∑ m ∈ S, f n m := by

  have houter : ∀ n, n ∉ S → (∑ m, f n m) = 0 := by
    intro n hn
    apply Finset.sum_eq_zero
    intro m _
    exact h n m (Or.inl hn)

  have hinner : ∀ n ∈ S, (∑ m, f n m) = ∑ m ∈ S, f n m := by
    intro n _
    apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro m _ hm
    exact h n m (Or.inr hm)
  calc (∑ n, ∑ m, f n m)
      = ∑ n ∈ S, ∑ m, f n m := by
        apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intro n _ hn
        exact houter n hn
    _ = ∑ n ∈ S, ∑ m ∈ S, f n m := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hinner n hn

theorem source_polynomial_postprocessing {I : Type*} (S : Finset I) (K ν c : ℕ)
    (hS : S.card ≤ K) (hK : K ≤ ν ^ c) :
    (S.product S).card ≤ ν ^ (2 * c) := by
  have hcard : (S.product S).card = S.card * S.card := Finset.card_product S S
  rw [hcard]
  calc S.card * S.card ≤ K * K := Nat.mul_le_mul hS hS
    _ ≤ ν ^ c * ν ^ c := Nat.mul_le_mul hK hK
    _ = ν ^ (2 * c) := by
        rw [← pow_add, show c + c = 2 * c by omega]

end Qatlib.Papers.ThermalRate98.MainResults
