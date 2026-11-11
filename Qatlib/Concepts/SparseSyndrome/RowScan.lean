/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ParityTester.SampledParity.SparseSyndromeDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Sparse binary syndrome scans and read bounds

This module connects scans of lists of parity-check indices with multiplication by the binary
`parityMatrix`. A scan records every index occurrence, so repeated indices contribute according
to their multiplicity. Binary parity checks and syndromes are basic ingredients of stabilizer
error correction [Gottesman1997].

The read log has length at most the number of rows times a uniform row-length bound. A uniform
bound on column reads also controls the Hamming weight of the syndrome change caused by an error
vector.

## Main statements

* `scanRow_parity_and_log`: the parity value and exact read log of one row.
* `scanRows_matrix_and_reads`: the syndrome matrix-vector product and row-sparsity read bound.
* `syndrome_change_le_column_reads`: Hamming stability under a bound on column reads.

## References

* [Gottesman, 1997][Gottesman1997]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.ParityTester.SampledParity
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.SparseSyndrome.RowScan
open Matrix
open scoped BigOperators

/-- Scanning one row returns the sum of the selected binary entries and records exactly the
row's index list. -/
private theorem scanRow_sum {n : ℕ} (x : Fin n → ZMod 2) (row : List (Fin n)) :
    (scanRow x row).1 = (row.map x).sum ∧ (scanRow x row).2 = row := by
  induction row with
  | nil => simp [scanRow]
  | cons i row ih => simp [scanRow, ih]

/-- A row scan computes the parity sum with each index weighted by its multiplicity and records
exactly the row's index list. -/
theorem scanRow_parity_and_log :
    ∀ (n : ℕ) (x : Fin n → ZMod 2) (row : List (Fin n)),
      (scanRow x row).1 = ∑ i : Fin n, (row.count i : ZMod 2) * x i ∧
        (scanRow x row).2 = row := by
  intro n x row
  obtain ⟨hv,hl⟩ := scanRow_sum x row
  refine ⟨hv.trans ?_,hl⟩
  calc
    (row.map x).sum = ∑ i ∈ row.toFinset, (row.count i : ZMod 2) * x i := by
      rw [Finset.sum_list_map_count]
      simp only [nsmul_eq_mul]
    _ = ∑ i : Fin n, (row.count i : ZMod 2) * x i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hz : row.count i = 0 := List.count_eq_zero.mpr (by simpa using hi)
      simp [hz]

/-- Scanning all rows returns their individual parity values and records the flattened list of
row indices. -/
private theorem scanRows_map {n : ℕ} (x : Fin n → ZMod 2)
    (rows : List (List (Fin n))) :
    (scanRows x rows).1 = rows.map (fun row => (scanRow x row).1) ∧
      (scanRows x rows).2 = rows.flatten := by
  induction rows with
  | nil => simp [scanRows]
  | cons row rows ih => simp [scanRows, ih, (scanRow_parity_and_log n x row).2]

/-- If every row has length at most `w`, the flattened list has length at most the number of
rows times `w`. -/
private theorem flatten_length_bound {α : Type*} (rows : List (List α)) (w : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ w) : rows.flatten.length ≤ rows.length*w := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun row hr => h row (by simp [hr]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Scanning all rows computes the parity matrix-vector product and records the flattened index
list, with at most rows.length times `w` reads when every row has length at most `w`. -/
theorem scanRows_matrix_and_reads :
    ∀ (n : ℕ) (x : Fin n → ZMod 2) (rows : List (List (Fin n))),
      (scanRows x rows).1 = List.ofFn (parityMatrix rows *ᵥ x) ∧
      (scanRows x rows).2 = rows.flatten ∧
      ∀ w : ℕ, (∀ row ∈ rows, row.length ≤ w) →
        (scanRows x rows).2.length ≤ rows.length * w := by
  intro n x rows
  obtain ⟨hv,hl⟩ := scanRows_map x rows
  refine ⟨hv.trans ?_,hl,fun w hw => ?_⟩
  · calc
      rows.map (fun row => (scanRow x row).1) =
          (List.ofFn rows.get).map (fun row => (scanRow x row).1) := by rw [List.ofFn_get]
      _ = List.ofFn (fun r => (scanRow x (rows.get r)).1) := by rw [List.map_ofFn]; rfl
      _ = List.ofFn (parityMatrix rows *ᵥ x) := by
        congr 1
        funext r
        exact (scanRow_parity_and_log n x (rows.get r)).1
  · rw [hl]
    exact flatten_length_bound rows w hw

/-- The Hamming weight of a sum of binary vectors is at most the sum of their Hamming weights. -/
private theorem weight_add_le {α : Type*} [Fintype α] (x y : α → ZMod 2) :
    bitWeight (x+y) ≤ bitWeight x + bitWeight y := by
  classical
  apply (Finset.card_le_card (show
    (Finset.univ.filter fun i => (x+y) i ≠ 0) ⊆
      (Finset.univ.filter fun i => x i ≠ 0) ∪ (Finset.univ.filter fun i => y i ≠ 0) from ?_)).trans
    (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hn
  push Not at hn
  exact hi (by simp [hn])

/-- The Hamming weight of a finite sum of binary vectors is at most the sum of their Hamming
weights. -/
private theorem weight_sum_le {α β : Type*} [Fintype α]
    (s : Finset β) (v : β → α → ZMod 2) :
    bitWeight (∑ i ∈ s, v i) ≤ ∑ i ∈ s, bitWeight (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitWeight]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (weight_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Summing the multiplicity of an index over all rows equals its multiplicity in the flattened
list. -/
private theorem sum_row_counts {n : ℕ} (rows : List (List (Fin n))) (i : Fin n) :
    (∑ r : Fin rows.length, (rows.get r).count i) = rows.flatten.count i := by
  induction rows with
  | nil => simp
  | cons row rows ih => simpa [Fin.sum_univ_succ, List.count_append] using congrArg (fun k => row.count i+k) ih

/-- The Hamming weight of a parity-matrix column multiplied by a binary scalar is at most the
number of reads of that column. -/
private theorem column_weight_le {n : ℕ} (rows : List (List (Fin n)))
    (i : Fin n) (b : ZMod 2) :
    bitWeight (fun r => parityMatrix rows r i*b) ≤ columnReads rows i := by
  classical
  let s := Finset.univ.filter fun r : Fin rows.length => parityMatrix rows r i*b ≠ 0
  have hpos (r : Fin rows.length) (hr : r ∈ s) : 1 ≤ (rows.get r).count i := by
    have hn : (rows.get r).count i ≠ 0 := by
      intro hz
      have hr' : parityMatrix rows r i*b ≠ 0 := (Finset.mem_filter.mp hr).2
      apply hr'
      change ((rows.get r).count i : ZMod 2)*b = 0
      simp only [hz, Nat.cast_zero, zero_mul]
    omega
  calc
    bitWeight (fun r => parityMatrix rows r i*b) = ∑ _r ∈ s, 1 := by simp [bitWeight,s]
    _ ≤ ∑ r ∈ s, (rows.get r).count i := Finset.sum_le_sum hpos
    _ ≤ ∑ r : Fin rows.length, (rows.get r).count i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = columnReads rows i := sum_row_counts rows i

/-- If each column is read at most `d` times, adding an error vector changes at most `d` times
its Hamming weight many syndrome bits. -/
theorem syndrome_change_le_column_reads :
    ∀ (n : ℕ) (rows : List (List (Fin n))) (d : ℕ),
      (∀ i : Fin n, columnReads rows i ≤ d) →
      ∀ x e : Fin n → ZMod 2,
        bitWeight (parityMatrix rows *ᵥ (x+e)-parityMatrix rows *ᵥ x) ≤ d*bitWeight e := by
  intro n rows d hd x e
  classical
  rw [Matrix.mulVec_add, add_sub_cancel_left]
  have heq : parityMatrix rows *ᵥ e = ∑ i : Fin n, (fun r => parityMatrix rows r i*e i) := by
    funext r
    simp [Matrix.mulVec, dotProduct]
  rw [heq]
  calc
    bitWeight (∑ i : Fin n, (fun r => parityMatrix rows r i*e i)) ≤
        ∑ i : Fin n, bitWeight (fun r => parityMatrix rows r i*e i) := weight_sum_le _ _
    _ ≤ ∑ i : Fin n, if e i = 0 then 0 else d := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : e i = 0
      · simp [hi,bitWeight]
      · rw [if_neg hi]
        exact (column_weight_le rows i (e i)).trans (hd i)
    _ = d*bitWeight e := by
      simp [bitWeight, Finset.sum_ite, Nat.mul_comm]

end Qatlib.Concepts.SparseSyndrome.RowScan
