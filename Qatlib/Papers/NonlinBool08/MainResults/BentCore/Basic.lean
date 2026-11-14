/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Binary characters and the Walsh transform

Defines binary vectors `BVec`, their sign characters `wchi`, and the integer-valued Walsh
transform `walsh`. Character orthogonality supplies the basic finite Fourier identities, while
`Bent` records a flat squared spectrum and `IsDual` records its Boolean sign function. See
[Roetteler2008].

## Main statements

* `sum_eps_dot`: binary characters sum to zero at nonzero frequencies.
* `Bent`: all squared Walsh coefficients equal 2^n.
* `IsDual`: a Boolean function describes the signs of the normalized Walsh spectrum.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.BentCore

/-- Binary vectors of length `n`, represented as functions from `Fin n` to `ZMod 2`. -/
abbrev BVec (n : ℕ) : Type := Fin n → ZMod 2

/-- The dot product of binary vectors with values in `ZMod 2`. -/
abbrev dot {n : ℕ} (x y : BVec n) : ZMod 2 := dotProduct x y

/-- Every element of `ZMod 2` is zero or one. -/
lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hlt : z.val < 2 := ZMod.val_lt z
  have hcast : ((z.val : ℕ) : ZMod 2) = z := ZMod.natCast_zmod_val z
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
  · left
    rw [← hcast, show z.val = 0 from by omega]
    simp
  · right
    rw [← hcast, h]
    norm_num

/-- Adding one to itself in `ZMod 2` gives zero. -/
lemma one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

/-- The additive inverse of one in `ZMod 2` is one. -/
lemma neg_one_zmod2 : -(1 : ZMod 2) = 1 := by decide

/-- The integer sign character of `ZMod 2`, taking zero to one and one to negative one. -/
def eps (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

/-- The sign character takes zero to one. -/
@[simp] lemma eps_zero : eps 0 = 1 := by simp [eps]

/-- The sign character takes one to negative one. -/
@[simp] lemma eps_one : eps 1 = -1 := by
  have h : (1 : ZMod 2) ≠ 0 := by decide
  simp [eps, h]

/-- The sign character sends binary addition to multiplication of integer signs. -/
lemma eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [eps, one_add_one_zmod2]

/-- Negating a binary value leaves its sign character unchanged. -/
lemma eps_neg (z : ZMod 2) : eps (-z) = eps z := by
  rcases zmod2_cases z with rfl | rfl <;> simp [eps]

/-- The sign of a binary difference equals the sign of the corresponding sum. -/
lemma eps_sub (a b : ZMod 2) : eps (a - b) = eps (a + b) := by
  rw [sub_eq_add_neg, eps_add, eps_neg, ← eps_add]

/-- The square of every value of the sign character is one. -/
@[simp] lemma eps_sq (z : ZMod 2) : eps z ^ 2 = 1 := by
  rcases zmod2_cases z with rfl | rfl <;> simp [eps]

/-- Every value of the sign character has absolute value one. -/
lemma abs_eps (z : ZMod 2) : |eps z| = 1 := by
  rcases zmod2_cases z with rfl | rfl <;> simp [eps]

/-- The additive character on binary vectors given by the sign of the dot product with `w`. -/
def wchi {n : ℕ} (w : BVec n) : AddChar (BVec n) ℤ where
  toFun := fun x => eps (dot w x)
  map_zero_eq_one' := by simp [dot, eps]
  map_add_eq_mul' := by
    intro x y
    simp only [dot]
    rw [dotProduct_add, eps_add]

/-- The dot product with a vector supported at coordinate `i` is `w i * c`. -/
lemma dot_single {n : ℕ} (w : BVec n) (i : Fin n) (c : ZMod 2) :
    dot w (Pi.single i c) = w i * c := by
  rw [dot, dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [ hj]
  · intro hi
    simp at hi

/-- The character at zero frequency is identically one. -/
@[simp] lemma wchi_zero_apply {n : ℕ} (x : BVec n) : wchi (0 : BVec n) x = 1 := by
  simp [wchi, dot, eps]

/-- The character `wchi w` is the trivial additive character exactly when `w` is zero. -/
lemma wchi_eq_zero_iff {n : ℕ} (w : BVec n) : wchi w = 0 ↔ w = 0 := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw (funext fun j => hc j)
    have hw1 : w i = 1 := by
      rcases zmod2_cases (w i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    have hval : wchi w (Pi.single i (1 : ZMod 2)) = eps (w i * 1) := by
      show eps (dot w (Pi.single i (1 : ZMod 2))) = eps (w i * 1)
      rw [dot_single]
    have htriv : wchi w (Pi.single i (1 : ZMod 2)) = 1 := by
      rw [h]
      simp
    rw [hval, hw1] at htriv
    norm_num [eps] at htriv
  · rintro rfl
    ext x
    simp [wchi, dot, eps]

/-- The cardinality of the binary vector space, cast to the integers, is `2 ^ n`. -/
lemma card_bvec (n : ℕ) : (Fintype.card (BVec n) : ℤ) = 2 ^ n := by
  simp [BVec]

/-- There are `2 ^ n` binary vectors of length `n`. -/
lemma card_bvec_nat (n : ℕ) : Fintype.card (BVec n) = 2 ^ n := by
  exact_mod_cast card_bvec n

/-- The sum of a binary dot-product character is `2 ^ n` at zero frequency and zero at every
other frequency. -/
lemma sum_eps_dot {n : ℕ} (v : BVec n) :
    ∑ x : BVec n, eps (dot v x) = if v = 0 then 2 ^ n else 0 := by
  classical
  have hsum : (∑ x : BVec n, eps (dot v x)) = ∑ x : BVec n, wchi v x := rfl
  rw [hsum, AddChar.sum_eq_ite]
  by_cases hv : v = 0
  · have hz : wchi v = 0 := (wchi_eq_zero_iff v).mpr hv
    rw [ite_eq_left hz, ite_eq_left hv, card_bvec]
  · have hz : wchi v ≠ 0 := fun h => hv ((wchi_eq_zero_iff v).mp h)
    rw [ite_eq_right hz, ite_eq_right hv]

/-- The unnormalized integer Walsh coefficient obtained by summing the product of the frequency
character and the sign of `f`. -/
def walsh {n : ℕ} (f : BVec n → ZMod 2) (w : BVec n) : ℤ :=
  ∑ x, eps (dot w x) * eps (f x)

/-- A Walsh coefficient is the sum of signs of `dot w x + f x`. -/
lemma walsh_eq_sum_eps_add {n : ℕ} (f : BVec n → ZMod 2) (w : BVec n) :
    walsh f w = ∑ x, eps (dot w x + f x) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [eps_add]

/-- The condition that every squared Walsh coefficient of `f` equals `2 ^ n`. -/
def Bent {n : ℕ} (f : BVec n → ZMod 2) : Prop :=
  ∀ w, walsh f w ^ 2 = 2 ^ n

/-- The condition that the Walsh coefficient of `f` at `w` equals `2 ^ (n / 2)` times the sign
of `ftilde w`. -/
def IsDual {n : ℕ} (f : BVec n → ZMod 2) (ftilde : BVec n → ZMod 2) : Prop :=
  ∀ w, walsh f w = (2 : ℤ) ^ (n / 2) * eps (ftilde w)

end Qatlib.Papers.NonlinBool08.MainResults.BentCore
