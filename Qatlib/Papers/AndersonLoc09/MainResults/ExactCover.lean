/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

structure Clause (N : ℕ) where

  i : Fin N

  j : Fin N

  k : Fin N

  hij : i ≠ j

  hik : i ≠ k

  hjk : j ≠ k
deriving DecidableEq

def clauseCost {N : ℕ} (x : Fin N → ℤ) (c : Clause N) : ℤ :=
  (x c.i + x c.j + x c.k - 1) ^ 2

theorem clauseCost_nonneg {N : ℕ} (x : Fin N → ℤ) (c : Clause N) :
    0 ≤ clauseCost x c := by
  unfold clauseCost
  exact sq_nonneg _

theorem clauseCost_eq_zero_iff {N : ℕ} (x : Fin N → ℤ) (c : Clause N)
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    clauseCost x c = 0 ↔ x c.i + x c.j + x c.k = 1 := by
  rcases hx c.i with hi | hi <;> rcases hx c.j with hj | hj <;>
    rcases hx c.k with hk | hk <;> simp [clauseCost, hi, hj, hk]

theorem clauseCost_eq_zero_or_one_or_four {N : ℕ} (x : Fin N → ℤ) (c : Clause N)
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    clauseCost x c = 0 ∨ clauseCost x c = 1 ∨ clauseCost x c = 4 := by
  rcases hx c.i with hi | hi <;> rcases hx c.j with hj | hj <;>
    rcases hx c.k with hk | hk <;> simp [clauseCost, hi, hj, hk]

theorem clauseCost_eq_four_iff {N : ℕ} (x : Fin N → ℤ) (c : Clause N)
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    clauseCost x c = 4 ↔ x c.i = 1 ∧ x c.j = 1 ∧ x c.k = 1 := by
  rcases hx c.i with hi | hi <;> rcases hx c.j with hj | hj <;>
    rcases hx c.k with hk | hk <;> simp [clauseCost, hi, hj, hk]

theorem clauseCost_le_four {N : ℕ} (x : Fin N → ℤ) (c : Clause N)
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    clauseCost x c ≤ 4 := by
  rcases clauseCost_eq_zero_or_one_or_four x c hx with h | h | h <;> omega

def instanceCost {N : ℕ} (x : Fin N → ℤ) (cs : Finset (Clause N)) : ℤ :=
  ∑ c ∈ cs, clauseCost x c

theorem instanceCost_nonneg {N : ℕ} (x : Fin N → ℤ) (cs : Finset (Clause N)) :
    0 ≤ instanceCost x cs := by
  unfold instanceCost
  exact Finset.sum_nonneg fun c _ => clauseCost_nonneg x c

theorem instanceCost_eq_zero_iff {N : ℕ} (x : Fin N → ℤ) (cs : Finset (Clause N))
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    instanceCost x cs = 0 ↔ ∀ c ∈ cs, x c.i + x c.j + x c.k = 1 := by
  unfold instanceCost
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => clauseCost_nonneg x c)]
  constructor
  · intro h c hc
    exact (clauseCost_eq_zero_iff x c hx).mp (h c hc)
  · intro h c hc
    exact (clauseCost_eq_zero_iff x c hx).mpr (h c hc)

theorem clause_energy_eq_ising (s₁ s₂ s₃ : ℝ)
    (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) (h₃ : s₃ = 1 ∨ s₃ = -1) :
    ((1 - s₁) / 2 + (1 - s₂) / 2 + (1 - s₃) / 2 - 1) ^ 2
      = 1 - (s₁ + s₂ + s₃) / 2 + (s₁ * s₂ + s₁ * s₃ + s₂ * s₃) / 2 := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;>
    subst h₁ <;> subst h₂ <;> subst h₃ <;> norm_num

theorem separates_of_patterns {N : ℕ} (x y : Fin N → ℤ) (c : Clause N)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hxi : x c.i = 1) (hxj : x c.j = 0) (hxk : x c.k = 0)
    (hyi : y c.i = 0) (hyj : y c.j = 0) (hyk : y c.k = 0) :
    clauseCost x c = 0 ∧ clauseCost y c ≠ 0 := by
  constructor
  · rw [clauseCost_eq_zero_iff x c hx]
    simp [hxi, hxj, hxk]
  · intro h
    have hzero := (clauseCost_eq_zero_iff y c hy).mp h
    simp [hyi, hyj, hyk] at hzero

theorem satPattern_card :
    (Finset.univ.filter (fun p : Fin 3 → Bool =>
      (Finset.univ.filter (fun i => p i = true)).card = 1)).card = 3 := by
  decide

end Qatlib.Papers.AndersonLoc09.MainResults
