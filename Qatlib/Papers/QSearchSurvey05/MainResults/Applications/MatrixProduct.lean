/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Matrix product witnesses and subset sampling

This module encodes Boolean matrix multiplication over ZMod 2 as a mismatch search relation and
develops the subset counting estimates used in the matrix product application of [Ambainis2005].
The theorems `marked_frac_ge_single` and `matrix_product_query_bound` give the marked fraction
lower bound (k/n)² and the algebraic cost identity n^(2/3)n = n^(5/3).

## Main statements

* `theorem45_matrix_product`: Collects the equivalence between multiplication correctness and
  absence of mismatch witnesses.
* `marked_frac_ge_single`: Bounds the fraction of subset pairs containing a mismatch.
* `matrix_product_query_bound`: Simplifies the resulting scalar cost expression.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- Three n by n Boolean matrices forming an instance of matrix product verification. -/
structure MatrixProductInput (n : ℕ) where

  A : Matrix (Fin n) (Fin n) Bool

  B : Matrix (Fin n) (Fin n) Bool

  C : Matrix (Fin n) (Fin n) Bool

/-- An input entry address consisting of a matrix selector in `Fin 3` and a row and column
index. -/
abbrev MatrixProductIndex (n : ℕ) := Fin 3 × Fin n × Fin n

/-- Reads the addressed entry from A, B, or C according to the matrix selector. -/
def matrixProductEntry {n : ℕ} (X : MatrixProductInput n)
    (p : MatrixProductIndex n) : Bool :=
  if p.1 = 0 then X.A p.2.1 p.2.2
  else if p.1 = 1 then X.B p.2.1 p.2.2
  else X.C p.2.1 p.2.2

/-- The addresses in C where multiplication of A and B over `ZMod 2` disagrees with C. -/
def matrixProductMismatch {n : ℕ} (X : MatrixProductInput n) :
    Finset (MatrixProductIndex n) :=
  Finset.univ.filter fun p =>
    p.1 = 2 ∧
      (∑ k : Fin n, bitToZMod2 (X.A p.2.1 k) * bitToZMod2 (X.B k p.2.2)) ≠
        bitToZMod2 (X.C p.2.1 p.2.2)

/-- The full address set when the matrix product holds, and the mismatch addresses otherwise. -/
def matrixProductAccept {n : ℕ} (X : MatrixProductInput n) :
    Finset (MatrixProductIndex n) :=
  if MatrixProductHolds X.A X.B X.C then Finset.univ else matrixProductMismatch X

/-- The mismatch set is empty exactly when the matrix product holds over `ZMod 2`. See
[Ambainis2005]. -/
theorem matrixProductMismatch_eq_empty_iff {n : ℕ} (X : MatrixProductInput n) :
    matrixProductMismatch X = ∅ ↔ MatrixProductHolds X.A X.B X.C := by
  constructor
  · intro h i j
    by_contra hne
    have hmem : (((2 : Fin 3), i, j) : MatrixProductIndex n) ∈ matrixProductMismatch X := by
      rw [matrixProductMismatch, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl, hne⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [matrixProductMismatch, Finset.mem_filter] at hp
    obtain ⟨-, hp1, hp2⟩ := hp
    by_cases h2 : p.1 = 2
    · exact hp2 (h p.2.1 p.2.2)
    · exact h2 hp1

/-- If the matrix product holds, every input address belongs to the acceptance set. -/
theorem matrixProductAccept_of_holds {n : ℕ} {X : MatrixProductInput n}
    (h : MatrixProductHolds X.A X.B X.C) :
    matrixProductAccept X = Finset.univ := by
  simp [matrixProductAccept, h]

/-- If the matrix product fails, the acceptance set equals the mismatch set. -/
theorem matrixProductAccept_of_not_holds {n : ℕ} {X : MatrixProductInput n}
    (h : ¬ MatrixProductHolds X.A X.B X.C) :
    matrixProductAccept X = matrixProductMismatch X := by
  simp [matrixProductAccept, h]

/-- A failed matrix product has a nonempty acceptance set. -/
theorem matrixProductAccept_nonempty_of_not_holds {n : ℕ} {X : MatrixProductInput n}
    (h : ¬ MatrixProductHolds X.A X.B X.C) :
    (matrixProductAccept X).Nonempty := by
  rw [matrixProductAccept_of_not_holds h]
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  exact h ((matrixProductMismatch_eq_empty_iff X).mp he)

/-- For a failed matrix product, every accepted address selects C and witnesses an entrywise
disagreement with A times B over `ZMod 2`. See [Ambainis2005]. -/
theorem matrixProductAccept_witness {n : ℕ} {X : MatrixProductInput n}
    (h : ¬ MatrixProductHolds X.A X.B X.C) {p : MatrixProductIndex n}
    (hp : p ∈ matrixProductAccept X) :
    p.1 = 2 ∧
      (∑ k : Fin n, bitToZMod2 (X.A p.2.1 k) * bitToZMod2 (X.B k p.2.2)) ≠
        bitToZMod2 (X.C p.2.1 p.2.2) := by
  rw [matrixProductAccept_of_not_holds h] at hp
  rw [matrixProductMismatch, Finset.mem_filter] at hp
  exact hp.2

/-- For positive n, decomposes n^(5/3) as n times n^(2/3). -/
theorem matrixProduct_budget_decomposition (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ ((5 : ℝ) / 3) = (n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show (5 : ℝ) / 3 = 1 + 2 / 3 by norm_num, Real.rpow_add hpos, Real.rpow_one]

/-- Collects the mismatch characterization of matrix product correctness, the corresponding
acceptance sets, and nonemptiness and selector correctness when multiplication fails. See
[Ambainis2005]. -/
theorem theorem45_matrix_product (n : ℕ) (X : MatrixProductInput n) :
    (MatrixProductHolds X.A X.B X.C ↔ matrixProductMismatch X = ∅) ∧
      (MatrixProductHolds X.A X.B X.C → matrixProductAccept X = Finset.univ) ∧
      (¬ MatrixProductHolds X.A X.B X.C → matrixProductAccept X = matrixProductMismatch X) ∧
      (¬ MatrixProductHolds X.A X.B X.C → (matrixProductAccept X).Nonempty) ∧
      (∀ p ∈ matrixProductAccept X, ¬ MatrixProductHolds X.A X.B X.C → p.1 = 2) := by
  refine ⟨(matrixProductMismatch_eq_empty_iff X).symm, matrixProductAccept_of_holds,
    matrixProductAccept_of_not_holds, matrixProductAccept_nonempty_of_not_holds, ?_⟩
  intro p hp hne
  exact (matrixProductAccept_witness hne hp).1

/-- The number of k element subsets of `Fin n` containing a fixed index is (n − 1) choose (k −
1), for 1 ≤ k ≤ n. -/
theorem card_containing (n : ℕ) (i : Fin n) (k : ℕ) (hk : 1 ≤ k) (_hkn : k ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun R => i ∈ R)).card
      = (n - 1).choose (k - 1) := by
  have h := Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n)) Finset.univ k
    (by simp) (by simpa using hk)
  simpa [Finset.card_univ, Finset.card_singleton, Finset.singleton_subset_iff] using h

/-- For 1 ≤ k ≤ n, the rational ratio of (n − 1) choose (k − 1) to n choose k equals k/n. -/
theorem ratio_choose (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n - 1).choose (k - 1) : ℚ) / (n.choose k : ℚ) = (k : ℚ) / n := by
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hk hkn)
  have hid : (n : ℚ) * ((n - 1).choose (k - 1) : ℚ) = (n.choose k : ℚ) * (k : ℚ) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    have hn1 : (n - 1) + 1 = n := by omega
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hn1, hk1] at h
    exact_mod_cast h
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hc0 : (n.choose k : ℚ) ≠ 0 := by
    have : 0 < n.choose k := Nat.choose_pos hkn
    exact_mod_cast ne_of_gt this
  field_simp
  linear_combination hid

/-- The finite set of all k element subsets of `Fin n`. -/
def kSubsets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard k

/-- The pairs of k element subsets whose Cartesian product contains an element of W. -/
def markedPairs (n k : ℕ) (W : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((kSubsets n k) ×ˢ (kSubsets n k)).filter
    (fun p => ∃ x ∈ W, x.1 ∈ p.1 ∧ x.2 ∈ p.2)

/-- For a singleton witness (i, j), marked subset pairs are exactly those whose first subset
contains i and whose second subset contains j. -/
theorem markedPairs_single (n k : ℕ) (_hk : 1 ≤ k) (_hkn : k ≤ n) (i j : Fin n) :
    markedPairs n k {(i, j)}
      = ((kSubsets n k).filter (fun R => i ∈ R)) ×ˢ
        ((kSubsets n k).filter (fun S => j ∈ S)) := by
  rw [markedPairs]
  have hcongr : ((kSubsets n k) ×ˢ (kSubsets n k)).filter
        (fun p => ∃ x ∈ ({(i, j)} : Finset (Fin n × Fin n)), x.1 ∈ p.1 ∧ x.2 ∈ p.2)
      = ((kSubsets n k) ×ˢ (kSubsets n k)).filter (fun p => i ∈ p.1 ∧ j ∈ p.2) := by
    apply Finset.filter_congr
    intro p _
    simp
  rw [hcongr]
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hR, hS⟩, hi, hj⟩
    exact ⟨⟨hR, hi⟩, ⟨hS, hj⟩⟩
  · rintro ⟨⟨hR, hi⟩, ⟨hS, hj⟩⟩
    exact ⟨⟨hR, hS⟩, hi, hj⟩

/-- For 1 ≤ k ≤ n, the number of subset pairs marked by a singleton witness is the square of (n
− 1) choose (k − 1). -/
theorem markedPairs_single_card (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (i j : Fin n) :
    (markedPairs n k {(i, j)}).card = (n - 1).choose (k - 1) * (n - 1).choose (k - 1) := by
  rw [markedPairs_single n k hk hkn i j, Finset.card_product]
  simp only [kSubsets]
  rw [card_containing n i k hk hkn, card_containing n j k hk hkn]

/-- There are n choose k subsets of `Fin n` with cardinality k. -/
theorem kSubsets_card (n k : ℕ) : (kSubsets n k).card = n.choose k := by
  simp [kSubsets]

/-- For 1 ≤ k ≤ n, the fraction of subset pairs containing a fixed witness is exactly (k/n)².
See [Ambainis2005]. -/
theorem single_entry_prob_sq (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (i j : Fin n) :
    ((markedPairs n k {(i, j)}).card : ℚ) /
        (((kSubsets n k) ×ˢ (kSubsets n k)).card : ℚ) = ((k : ℚ) / n) ^ 2 := by
  have hkey : (((n - 1).choose (k - 1) : ℕ) : ℚ) / ((n.choose k : ℕ) : ℚ) = (k : ℚ) / n :=
    ratio_choose n k hk hkn
  rw [markedPairs_single_card n k hk hkn i j, Finset.card_product, kSubsets_card]
  push_cast
  rw [← div_mul_div_comm, hkey]
  ring

/-- For k ≤ n, the total number of pairs of k element subsets is positive. -/
theorem markedPairs_total_pos (n k : ℕ) (hkn : k ≤ n) :
    (0 : ℚ) < (((kSubsets n k) ×ˢ (kSubsets n k)).card : ℚ) := by
  have hD : (((kSubsets n k) ×ˢ (kSubsets n k)).card : ℚ)
      = (n.choose k : ℚ) * (n.choose k : ℚ) := by
    rw [Finset.card_product, kSubsets_card]; push_cast; ring
  have hcp : (0 : ℚ) < (n.choose k : ℚ) := by
    exact_mod_cast Nat.choose_pos hkn
  rw [hD]; exact mul_pos hcp hcp

/-- Enlarging the witness set cannot decrease the number of marked subset pairs. -/
theorem markedPairs_mono (n k : ℕ) (W W' : Finset (Fin n × Fin n)) (h : W ⊆ W') :
    (markedPairs n k W).card ≤ (markedPairs n k W').card := by
  apply Finset.card_le_card
  intro p hp
  simp only [markedPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨hp.1, hp.2.imp (fun x hx => ⟨h hx.1, hx.2⟩)⟩

/-- For a nonempty witness set and 1 ≤ k ≤ n, the marked fraction of subset pairs is at least
(k/n)². See [Ambainis2005]. -/
theorem marked_frac_ge_single (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (W : Finset (Fin n × Fin n)) (hW : W.Nonempty) :
    ((k : ℚ) / n) ^ 2 ≤ ((markedPairs n k W).card : ℚ) /
        (((kSubsets n k) ×ˢ (kSubsets n k)).card : ℚ) := by
  obtain ⟨x, hx⟩ := hW
  obtain ⟨i, j⟩ := x
  have hsub : ({(i, j)} : Finset (Fin n × Fin n)) ⊆ W :=
    Finset.singleton_subset_iff.mpr hx
  have hmono : (markedPairs n k {(i, j)}).card ≤ (markedPairs n k W).card :=
    markedPairs_mono n k _ _ hsub
  have hmonoQ : ((markedPairs n k {(i, j)}).card : ℚ) ≤ ((markedPairs n k W).card : ℚ) := by
    exact_mod_cast hmono
  have hsingle : ((k : ℚ) / n) ^ 2
      = ((markedPairs n k {(i, j)}).card : ℚ) /
        (((kSubsets n k) ×ˢ (kSubsets n k)).card : ℚ) :=
    (single_entry_prob_sq n k hk hkn i j).symm
  have hDpos := markedPairs_total_pos n k hkn
  rw [hsingle]
  exact div_le_div_of_nonneg_right hmonoQ (le_of_lt hDpos)

/-- For positive n, the square root of n^(2/3) equals n^(1/3). -/
theorem sqrt_rpow_two_thirds (n : ℝ) (hn : 0 < n) :
    Real.sqrt (n ^ (2/3:ℝ)) = n ^ (1/3:ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hn)]
  norm_num

/-- For positive n, dividing n by the square root of n^(2/3) gives n^(2/3). See [Ambainis2005]. -/
theorem iterations_at_threshold (n : ℝ) (hn : 0 < n) :
    n / Real.sqrt (n ^ (2/3:ℝ)) = n ^ (2/3:ℝ) := by
  rw [sqrt_rpow_two_thirds n hn,
    div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hn _)),
    ← Real.rpow_add hn]
  norm_num

/-- For positive n, n^(2/3) times n equals n^(5/3). See [Ambainis2005]. -/
theorem total_cost_rpow (n : ℝ) (hn : 0 < n) :
    n ^ (2/3:ℝ) * n = n ^ (5/3:ℝ) := by
  calc n ^ (2/3:ℝ) * n = n ^ (2/3:ℝ) * n ^ (1:ℝ) := by rw [Real.rpow_one]
    _ = n ^ ((2:ℝ)/3 + 1) := by rw [Real.rpow_add hn]
    _ = n ^ (5/3:ℝ) := by rw [show (2:ℝ)/3 + 1 = 5/3 by norm_num]

/-- Simplifies the scalar query cost n^(2/3)n to n^(5/3) for positive n. -/
theorem matrix_product_query_bound (n : ℝ) (hn : 0 < n) :
    n ^ (2/3:ℝ) * n = n ^ (5/3:ℝ) :=
  total_cost_rpow n hn

end Qatlib.Papers.QSearchSurvey05.MainResults
