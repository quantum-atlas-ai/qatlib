/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.SignedWtEnum99.MainResults.Pauli

/-!
# Quadratically signed weight enumerators

`qsen` is an integer sum over the kernel of a binary matrix, weighted by Hamming weight and the
sign of a binary quadratic form. The module also defines triangular and diagonal matrix parts
and the magnitude promise used in the associated decision problems. See [KnillLaflamme1999] for
the source development.

## Main statements

* `sum_weight`: evaluates the unrestricted binary weight sum as `(x + y) ^ n`.
* `abs_qsen_le`: bounds the magnitude of the signed enumerator by `(|x| + |y|) ^ n`.
* `PromiseHolds`: expresses the prescribed magnitude threshold for a signed sum.

## References

* [Knill and Laflamme, 1999][KnillLaflamme1999]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

open Pauli

/-- The Hamming weight of a binary vector, counting its coordinates equal to one. -/
def bitWeight {n : ℕ} (b : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => b i = 1)).card

/-- The binary quadratic form `bᵀ * B * b`, expressed as a coordinate sum. -/
def quadForm {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, b i * (B.mulVec b) i

/-- The integer sign of a binary scalar, equal to one at zero and negative one otherwise. -/
def sgnZ (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

/-- The integer signed Hamming-weight sum over the kernel of `A`, with quadratic sign from `B`
and weight parameters `x, y`. -/
def qsen {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : ℤ) : ℤ :=
  ∑ b : Fin n → ZMod 2,
    if A.mulVec b = 0 then
      sgnZ (quadForm B b) * x ^ bitWeight b * y ^ (n - bitWeight b)
    else 0

/-- The strictly lower triangular part of a square matrix, with all other entries set to zero. -/
def lwtr {n : ℕ} {R : Type} [Zero R] (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if j < i then M i j else 0

/-- The diagonal part of a square matrix, with off-diagonal entries set to zero. -/
def diagMat {n : ℕ} {R : Type} [Zero R] (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then M i j else 0

/-- The real threshold `(k ^ 2 + l ^ 2) ^ (n / 2) / 2` for the magnitude promise. -/
def promiseThreshold (k l : ℤ) (n : ℕ) : ℝ :=
  ((k ^ 2 + l ^ 2 : ℤ) : ℝ) ^ ((n : ℝ) / 2) / 2

/-- The predicate that the absolute real value of the integer sum `S` is at least
`promiseThreshold k l n`. -/
def PromiseHolds (S : ℤ) (k l : ℤ) (n : ℕ) : Prop :=
  promiseThreshold k l n ≤ |(S : ℝ)|

/-- The predicate that the diagonal part of a binary square matrix is the identity matrix. -/
def IsUnitDiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  diagMat A = 1

/-- The integer sign of a binary scalar has absolute value one. -/
lemma abs_sgnZ (z : ZMod 2) : |sgnZ z| = 1 := by
  unfold sgnZ
  split <;> simp

/-- Summing `x ^ bitWeight b * y ^ (n - bitWeight b)` over all binary vectors of length `n`
gives `(x + y) ^ n`. -/
lemma sum_weight (n : ℕ) (x y : ℤ) :
    (∑ b : Fin n → ZMod 2, x ^ bitWeight b * y ^ (n - bitWeight b)) = (x + y) ^ n := by
  classical
  have hprod : ∀ b : Fin n → ZMod 2,
      (∏ i : Fin n, (if b i = 0 then y else x))
        = x ^ bitWeight b * y ^ (n - bitWeight b) := by
    intro b
    have hp : ∀ i : Fin n, (b i = 0) ↔ ¬ (b i = 1) := by
      intro i
      constructor
      · intro h hi
        rw [h] at hi
        exact one_ne_zero hi.symm
      · intro h
        rcases Pauli.ZMod2_cases (b i) with h0 | h1
        · exact h0
        · exact absurd h1 h
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => b i = 1)
      (f := fun i => if b i = 0 then y else x)
    have hleft : (∏ i ∈ Finset.univ.filter (fun i => b i = 1),
        (if b i = 0 then y else x)) = x ^ bitWeight b := by
      have hx : ∀ i ∈ Finset.univ.filter (fun i => b i = 1),
          (if b i = 0 then y else x) = x := by
        intro i hi
        have hi1 : b i = 1 := (Finset.mem_filter.mp hi).2
        have hne : b i ≠ 0 := by rw [hi1]; exact one_ne_zero
        rw [if_neg hne]
      rw [Finset.prod_congr rfl hx, Finset.prod_const]
      rfl
    have hright : (∏ i ∈ Finset.univ.filter (fun i => ¬ b i = 1),
        (if b i = 0 then y else x)) = y ^ (n - bitWeight b) := by
      have hy : ∀ i ∈ Finset.univ.filter (fun i => ¬ b i = 1),
          (if b i = 0 then y else x) = y := by
        intro i hi
        have hi1 : ¬ b i = 1 := (Finset.mem_filter.mp hi).2
        rw [if_pos]
        exact (hp i).mpr hi1
      rw [Finset.prod_congr rfl hy, Finset.prod_const]
      congr 1
      have hcard := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => b i = 1)
      rw [Finset.card_univ, Fintype.card_fin] at hcard
      unfold bitWeight
      omega
    rw [← hsplit, hleft, hright]
  have hsplit_all := Finset.prod_univ_sum
    (t := fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
    (f := fun (_ : Fin n) (z : ZMod 2) => if z = 0 then y else x)
  rw [Fintype.piFinset_univ] at hsplit_all
  have hinner : ∀ _ : Fin n, (∑ z : ZMod 2, (if z = 0 then y else x)) = x + y := by
    intro _
    have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [h]
    simp
    ring
  calc (∑ b : Fin n → ZMod 2, x ^ bitWeight b * y ^ (n - bitWeight b))
      = ∑ b : Fin n → ZMod 2, ∏ i : Fin n, (if b i = 0 then y else x) := by
        apply Finset.sum_congr rfl
        intro b _
        exact (hprod b).symm
    _ = ∏ i : Fin n, (∑ z : ZMod 2, (if z = 0 then y else x)) := hsplit_all.symm
    _ = ∏ _ : Fin n, (x + y) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hinner i
    _ = (x + y) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The absolute value of the signed weight enumerator is at most `(|x| + |y|) ^ n`. -/
theorem abs_qsen_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : ℤ) :
    |qsen A B x y| ≤ (|x| + |y|) ^ n := by
  classical
  have hterm : ∀ b : Fin n → ZMod 2,
      |(if A.mulVec b = 0 then
        sgnZ (quadForm B b) * x ^ bitWeight b * y ^ (n - bitWeight b) else 0)|
        ≤ |x| ^ bitWeight b * |y| ^ (n - bitWeight b) := by
    intro b
    by_cases hb : A.mulVec b = 0
    · rw [if_pos hb, abs_mul, abs_mul, abs_pow, abs_pow, abs_sgnZ, one_mul]
    · rw [if_neg hb, abs_zero]
      positivity
  calc |qsen A B x y|
      ≤ ∑ b : Fin n → ZMod 2,
          |(if A.mulVec b = 0 then
            sgnZ (quadForm B b) * x ^ bitWeight b * y ^ (n - bitWeight b) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Fin n → ZMod 2, |x| ^ bitWeight b * |y| ^ (n - bitWeight b) :=
        Finset.sum_le_sum (fun b _ => hterm b)
    _ = (|x| + |y|) ^ n := sum_weight n |x| |y|

end Qatlib.Papers.SignedWtEnum99.MainResults
