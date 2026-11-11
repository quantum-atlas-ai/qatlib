/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.QuantumLDPCDecoding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# OneShotLDPC23.MainResults.Model.BinaryWeight — binary weight algebra for §4

Fixed paper: Gu--Tang--Caha--Choe--He--Kubica, *Single-shot decoding of good
quantum LDPC codes*, **arXiv:2306.12470v2**.  This file supplies the elementary
`F₂`-vector weight algebra used by §4: `|x|` is the Hamming weight (`bitWeight`,
reused from `QltcQpcpBridge.CssTesters`), and
`overlap x y` is the size of the common support `|x ∩ y|`.

The two identities that drive Lemmas 4.12 and 4.13 are

* the symmetric-difference identity `|x + y| = |x| + |y| − 2|x ∩ y|`
  (`weight_add_exact`), and
* the union bound `|Σᵢ xᵢ| ≤ Σᵢ |xᵢ|` together with the overlap analogue
  `|z ∩ Σᵢ xᵢ| ≤ Σᵢ |z ∩ xᵢ|`.

Boundary: this module is pure combinatorics of `ZMod 2`-valued functions on a
finite type; it states nothing about Tanner codes or decoding.
-/

set_option autoImplicit false

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Model

/-- Binary vectors on the qubit register `Q` (`F₂^Q` in the paper). -/
abbrev BitVec (Q : Type*) := Q → ZMod 2

/-- Overlap `|x ∩ y|`: the number of positions where both `x` and `y` are nonzero. -/
def overlap {Q : Type*} [Fintype Q] (x y : BitVec Q) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0 ∧ y i ≠ 0).card

/-- Real-valued weight `|x|` (the paper writes `|x|`; reductions use `|e|_R`). -/
noncomputable def weightR {Q : Type*} [Fintype Q] (x : BitVec Q) : ℝ :=
  (bitWeight x : ℝ)

/-- Real-valued overlap. -/
noncomputable def overlapR {Q : Type*} [Fintype Q] (x y : BitVec Q) : ℝ :=
  (overlap x y : ℝ)

/-- The overlap of a vector with itself is its Hamming weight. -/
@[simp] theorem overlap_self {Q : Type*} [Fintype Q] (x : BitVec Q) :
    overlap x x = bitWeight x := by
  unfold overlap bitWeight
  congr 1
  ext i
  simp

/-- The Hamming weight of the zero vector is zero. -/
@[simp] theorem bitWeight_zero {Q : Type*} [Fintype Q] :
    bitWeight (0 : BitVec Q) = 0 := by
  unfold bitWeight
  simp

/-- The real-valued weight of the zero vector is zero. -/
@[simp] theorem weightR_zero {Q : Type*} [Fintype Q] :
    weightR (0 : BitVec Q) = 0 := by
  unfold weightR
  simp

/-- Overlap is symmetric. -/
theorem overlap_comm {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlap x y = overlap y x := by
  unfold overlap
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- Overlap is bounded by the weight of its left argument. -/
theorem overlap_le_left {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlap x y ≤ bitWeight x := by
  unfold overlap bitWeight
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.1

/-- Overlap is bounded by the weight of its right argument. -/
theorem overlap_le_right {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlap x y ≤ bitWeight y := by
  rw [overlap_comm]
  exact overlap_le_left y x

/-- The zero vector has zero overlap with any vector. -/
theorem overlap_zero_left {Q : Type*} [Fintype Q] (y : BitVec Q) :
    overlap (0 : BitVec Q) y = 0 := by
  unfold overlap
  simp

/-- Any vector has zero overlap with the zero vector. -/
theorem overlap_zero_right {Q : Type*} [Fintype Q] (x : BitVec Q) :
    overlap x (0 : BitVec Q) = 0 := by
  rw [overlap_comm, overlap_zero_left]

/-- Additivity of the support over a binary sum: the support of `x + y` is the
symmetric difference of the two supports, so `|x+y| + 2|x∩y| = |x| + |y|`. -/
theorem bitWeight_add_eq {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    bitWeight (x + y) + 2 * overlap x y = bitWeight x + bitWeight y := by
  have hx : bitWeight x = ∑ i : Q, if x i ≠ 0 then (1 : ℕ) else 0 := by
    unfold bitWeight
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hy : bitWeight y = ∑ i : Q, if y i ≠ 0 then (1 : ℕ) else 0 := by
    unfold bitWeight
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hxy : bitWeight (x + y) = ∑ i : Q, if (x + y) i ≠ 0 then (1 : ℕ) else 0 := by
    unfold bitWeight
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have ho : overlap x y = ∑ i : Q, if x i ≠ 0 ∧ y i ≠ 0 then (1 : ℕ) else 0 := by
    unfold overlap
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hx, hy, hxy, ho, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  have key : ∀ a b : ZMod 2,
      (if a + b ≠ 0 then (1 : ℕ) else 0) + 2 * (if a ≠ 0 ∧ b ≠ 0 then (1 : ℕ) else 0) =
        (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
    intro a b
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with rfl | rfl <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with rfl | rfl <;>
        decide
  exact key (x i) (y i)

/-- The paper's `|x̃| − |x̃ + y| = 2|x̃ ∩ y| − |y|`, in real arithmetic. -/
theorem weight_add_exact {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    weightR (x + y) = weightR x + weightR y - 2 * overlapR x y := by
  unfold weightR overlapR
  have h := bitWeight_add_eq x y
  have hcast : ((bitWeight (x + y) + 2 * overlap x y : ℕ) : ℝ) =
      (bitWeight x : ℝ) + (bitWeight y : ℝ) := by exact_mod_cast h
  push_cast at hcast
  linarith

/-- Subadditivity of the Hamming weight. -/
theorem bitWeight_add_le {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    bitWeight (x + y) ≤ bitWeight x + bitWeight y := by
  have h := bitWeight_add_eq x y
  omega

/-- Subadditivity in real form. -/
theorem weightR_add_le {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    weightR (x + y) ≤ weightR x + weightR y := by
  unfold weightR
  exact_mod_cast bitWeight_add_le x y

/-- Overlap is subadditive in its right slot. -/
theorem overlap_add_right_le {Q : Type*} [Fintype Q] [DecidableEq Q] (z x y : BitVec Q) :
    overlap z (x + y) ≤ overlap z x + overlap z y := by
  unfold overlap
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : x i = 0
  · right
    refine ⟨hi.1, ?_⟩
    · rw [Pi.add_apply, hx, zero_add] at hi
      exact hi.2
  · left
    exact ⟨hi.1, hx⟩

/-- Overlap is subadditive in its left slot. -/
theorem overlap_add_left_le {Q : Type*} [Fintype Q] [DecidableEq Q] (x y z : BitVec Q) :
    overlap (x + y) z ≤ overlap x z + overlap y z := by
  rw [overlap_comm (x + y) z, overlap_comm x z, overlap_comm y z]
  exact overlap_add_right_le z x y

/-- `|z ∩ Σᵢ xᵢ| ≤ Σᵢ |z ∩ xᵢ|` for a list of vectors. -/
theorem overlap_list_sum_le {Q : Type*} [Fintype Q] [DecidableEq Q]
    (z : BitVec Q) (l : List (BitVec Q)) :
    overlap z l.sum ≤ (l.map (overlap z)).sum := by
  induction l with
  | nil => simp [overlap_zero_right]
  | cons x xs ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    calc overlap z (x + xs.sum) ≤ overlap z x + overlap z xs.sum := overlap_add_right_le z x xs.sum
      _ ≤ overlap z x + (xs.map (overlap z)).sum := Nat.add_le_add_left ih _

/-- `|Σᵢ xᵢ| ≤ Σᵢ |xᵢ|` for a list of vectors. -/
theorem bitWeight_list_sum_le {Q : Type*} [Fintype Q] (l : List (BitVec Q)) :
    bitWeight l.sum ≤ (l.map bitWeight).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (bitWeight_add_le x xs.sum).trans (Nat.add_le_add_left ih _)

/-- Real form of `|Σᵢ xᵢ| ≤ Σᵢ |xᵢ|`. -/
theorem weightR_list_sum_le {Q : Type*} [Fintype Q] (l : List (BitVec Q)) :
    weightR l.sum ≤ (l.map weightR).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    have hw := weightR_add_le x xs.sum
    linarith

end Qatlib.Papers.OneShotLDPC23.MainResults.Model
