/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.PenaltyExact.Row
import Qatlib.Foundations.BooleanEnergy.HadamardGram.Energy
import Qatlib.Foundations.BooleanEnergy.HadamardGram.PairExpansion

/-!
# Exact penalties for a column pair

This module aggregates rowwise conjunction penalties and linear expressions for each column
pair. Valid ancillary bits recover the squared Gram entry, while a penalty coefficient greater
than the squared row count forces an invalid pair to have strictly greater energy; these
estimates support the quadratic reduction associated with [SuksmonoMinato2019].

## Main statements

* `paperPair_eq_squarePair`: Relate the two pair energies by a coefficient shift.
* `squarePair_compare`: Compare pair energy with the original squared Gram entry.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.HadamardGram

/-- For a given column pair, every ancillary bit equals the conjunction of its associated main
bits. -/
def PairValid {M N : ℕ} (x : Configuration M N) (p : ColumnPair N) : Prop :=
  ∀ r, ancilla x r p = (main x r (left p) && main x r (right p))

/-- The sum of rowwise conjunction penalties for a fixed column pair. -/
def pairPenalty {M N : ℕ} (x : Configuration M N) (p : ColumnPair N) : ℝ :=
  ∑ r, andPenalty (main x r (left p)) (main x r (right p)) (ancilla x r p)

/-- The sum of rowwise linear expressions for a fixed column pair. -/
def pairLinear {M N : ℕ} (x : Configuration M N) (p : ColumnPair N) : ℝ :=
  ∑ r, rowLinear (main x r (left p)) (main x r (right p)) (ancilla x r p)

/-- The squared pairwise linear sum plus `δ` times the conjunction penalty. -/
def squarePair {M N : ℕ} (δ : ℝ) (x : Configuration M N) (p : ColumnPair N) : ℝ :=
  pairLinear x p ^ 2 + δ * pairPenalty x p

/-- The constant row count plus twice the sum of products of rowwise linear expressions over row
pairs, with a `δ`-weighted penalty. -/
def paperPair {M N : ℕ} (δ : ℝ) (x : Configuration M N) (p : ColumnPair N) : ℝ :=
  (M : ℝ) + 2 * ∑ rp : ColumnPair M,
    rowLinear (main x (left rp) (left p)) (main x (left rp) (right p)) (ancilla x (left rp) p) *
    rowLinear (main x (right rp) (left p)) (main x (right rp) (right p)) (ancilla x (right rp) p) +
      δ * pairPenalty x p

/-- The conjunction penalty of a column pair is nonnegative. -/
theorem pairPenalty_nonneg {M N : ℕ} (x : Configuration M N) (p : ColumnPair N) :
    0 ≤ pairPenalty x p := Finset.sum_nonneg (fun _ _ => andPenalty_nonneg _ _ _)

/-- An invalid column pair has conjunction penalty at least one. -/
theorem pairPenalty_wrong {M N : ℕ} (x : Configuration M N) (p : ColumnPair N)
    (h : ¬PairValid x p) : 1 ≤ pairPenalty x p := by
  unfold PairValid at h
  push Not at h
  obtain ⟨r,hr⟩ := h
  exact (andPenalty_wrong _ _ _ hr).trans
    (Finset.single_le_sum (fun s _ => andPenalty_nonneg (main x s (left p))
      (main x s (right p)) (ancilla x s p)) (Finset.mem_univ r))

/-- A valid column pair has zero conjunction penalty. -/
theorem pairPenalty_valid {M N : ℕ} (x : Configuration M N) (p : ColumnPair N)
    (h : PairValid x p) : pairPenalty x p = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  rw [h r,andPenalty_correct]

/-- On a valid column pair, the linear sum equals the corresponding Gram entry of the main
matrix. -/
theorem pairLinear_valid {M N : ℕ} (x : Configuration M N) (p : ColumnPair N)
    (h : PairValid x p) : pairLinear x p = gram (main x) (left p) (right p) := by
  rw [gram_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [h r,rowLinear_correct]

/-- On a valid column pair, square-pair energy equals the square of the corresponding Gram
entry. -/
theorem squarePair_valid {M N : ℕ} (δ : ℝ) (x : Configuration M N) (p : ColumnPair N)
    (h : PairValid x p) : squarePair δ x p = gram (main x) (left p) (right p)^2 := by
  rw [squarePair,pairPenalty_valid x p h,pairLinear_valid x p h,mul_zero,add_zero]

/-- The paper-pair energy with coefficient `δ` equals the square-pair energy with coefficient `δ
- 8`. -/
theorem paperPair_eq_squarePair {M N : ℕ} (δ : ℝ) (x : Configuration M N) (p : ColumnPair N) :
    paperPair δ x p = squarePair (δ-8) x p := by
  let f : Fin M → ℝ := fun r =>
    rowLinear (main x r (left p)) (main x r (right p)) (ancilla x r p)
  have hs := sum_square_pairs M f
  have hd : (∑ r, f r^2) = (M : ℝ)+8*pairPenalty x p := by
    simp only [f,rowLinear_square,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    rw [← Finset.mul_sum]
    rfl
  rw [hd] at hs
  change (M : ℝ)+2*(∑ rp : ColumnPair M, f (left rp)*f (right rp)) +
    δ*pairPenalty x p = (∑ r, f r)^2+(δ-8)*pairPenalty x p
  rw [hs]
  ring

/-- For nonnegative `δ`, an invalid column pair has square-pair energy at least `δ`. -/
theorem squarePair_wrong_lower {M N : ℕ} (δ : ℝ) (hδ : 0 ≤ δ)
    (x : Configuration M N) (p : ColumnPair N) (h : ¬PairValid x p) : δ ≤ squarePair δ x p := by
  have hp := pairPenalty_wrong x p h
  have hm := mul_le_mul_of_nonneg_left hp hδ
  dsimp [squarePair]
  nlinarith [sq_nonneg (pairLinear x p)]

/-- If `δ > M ^ 2`, square-pair energy bounds the squared Gram entry from below, with strict
inequality for an invalid pair. -/
theorem squarePair_compare {M N : ℕ} (δ : ℝ) (hδ : (M : ℝ)^2 < δ)
    (x : Configuration M N) (p : ColumnPair N) :
    gram (main x) (left p) (right p)^2 ≤ squarePair δ x p ∧
      (¬PairValid x p → gram (main x) (left p) (right p)^2 < squarePair δ x p) := by
  classical
  by_cases hv : PairValid x p
  · exact ⟨(squarePair_valid δ x p hv).ge,fun h => False.elim (h hv)⟩
  · have hb := squarePair_wrong_lower δ (by nlinarith [sq_nonneg (M : ℝ)]) x p hv
    have hc := gram_sq_le (main x) (left p) (right p)
    exact ⟨by linarith,fun _ => by linarith⟩

/-- Every column pair in the completion of a Boolean matrix is valid. -/
theorem complete_pair_valid {M N : ℕ} (q : Fin M → Fin N → Bool) (p : ColumnPair N) :
    PairValid (complete q) p := by intro r; rfl

end Qatlib.Foundations.BooleanEnergy.PenaltyExact
