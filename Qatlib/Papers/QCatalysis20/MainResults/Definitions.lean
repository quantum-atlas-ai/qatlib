/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.BitVec

/-!
# LCU coefficients and sparse lookup addresses

This module defines finite linear combinations of matrices and their coefficient mass, together
with prefix offsets for ragged lookup tables. The address lemmas establish a bijective
flattening of valid address pairs and correctness of XOR lookup through the flattened table. See
[VonBurgEtAl2021].

## Main statements

* `coefficientMass_pos_of_exists`: The total coefficient mass is positive if some coefficient is
  nonzero.
* `multiplexedIndex_injective`: Equal flattened addresses with valid within-row indices have
  equal row indices and equal within-row indices.
* `lookup_chained_correct`: A flat table agreeing with the ragged table at every flattened
  address implements the same XOR lookup.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QCatalysis20.MainResults

/-- The finite linear combination of the matrices `U j` with complex coefficients `a j`. -/
def lcuOperator {J I : Type*} [Fintype J] (a : J → ℂ) (U : J → Matrix I I ℂ) :
    Matrix I I ℂ :=
  ∑ j, a j • U j

/-- The sum of the norms of the complex LCU coefficients. -/
def coefficientMass {J : Type*} [Fintype J] (a : J → ℂ) : ℝ := ∑ j, ‖a j‖

/-- The total coefficient mass is nonnegative. -/
@[simp] theorem coefficientMass_nonneg {J : Type*} [Fintype J] (a : J → ℂ) :
    0 ≤ coefficientMass a :=
  Finset.sum_nonneg fun j _ => norm_nonneg (a j)

/-- The total coefficient mass is positive if some coefficient is nonzero. -/
theorem coefficientMass_pos_of_exists {J : Type*} [Fintype J] {a : J → ℂ}
    (h : ∃ j, a j ≠ 0) :
    0 < coefficientMass a := by
  rcases h with ⟨j, hj⟩
  exact Finset.sum_pos' (fun i _ => norm_nonneg (a i)) ⟨j, Finset.mem_univ j, norm_pos_iff.mpr hj⟩

/-- The total number of entries in the first `J` rows of a ragged table with row lengths `K`. -/
def totalEntries (J : ℕ) (K : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range J, K j

/-- The number of entries in rows strictly before row `j`. -/
def prefixOffset (K : ℕ → ℕ) (j : ℕ) : ℕ := ∑ α ∈ Finset.range j, K α

/-- The prefix offset of the first row is zero. -/
@[simp] theorem prefixOffset_zero (K : ℕ → ℕ) : prefixOffset K 0 = 0 := by
  simp [prefixOffset]

/-- The next prefix offset is the current offset plus the current row length. -/
theorem prefixOffset_succ (K : ℕ → ℕ) (j : ℕ) :
    prefixOffset K (j + 1) = prefixOffset K j + K j := by
  simp [prefixOffset, Finset.sum_range_succ]

/-- Prefix offsets are monotone in the row index. -/
theorem prefixOffset_mono (K : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    prefixOffset K a ≤ prefixOffset K b :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

/-- A prefix ending no later than `J'` contains at most the total number of entries in the first
`J'` rows. -/
theorem prefixOffset_le_total {J J' : ℕ} (K : ℕ → ℕ) (h : J ≤ J') :
    prefixOffset K J ≤ totalEntries J' K := by
  simpa [totalEntries, prefixOffset] using
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      (fun _ _ _ => Nat.zero_le _))

/-- The flattened address obtained by adding a within-row index to its row's prefix offset. -/
def multiplexedIndex (K : ℕ → ℕ) (j k : ℕ) : ℕ := prefixOffset K j + k

/-- Every valid row and within-row address maps below the total entry count. -/
theorem multiplexedIndex_lt_total {J : ℕ} {K : ℕ → ℕ} {j k : ℕ}
    (hj : j < J) (hk : k < K j) :
    multiplexedIndex K j k < totalEntries J K := by
  have h1 : multiplexedIndex K j k < prefixOffset K (j + 1) := by
    rw [prefixOffset_succ]; unfold multiplexedIndex; omega
  have h2 : prefixOffset K (j + 1) ≤ totalEntries J K :=
    prefixOffset_le_total K (by omega)
  omega

/-- The flattened address of a valid entry as an element of `Fin (totalEntries J K)`. -/
def multiplexedIndexFin (J : ℕ) (K : ℕ → ℕ) (j : ℕ) (k : Fin (K j))
    (hj : j < J) : Fin (totalEntries J K) :=
  ⟨multiplexedIndex K j k.val, multiplexedIndex_lt_total hj k.isLt⟩

/-- If one row precedes another, the end of the earlier row is at most the later row's prefix
offset. -/
theorem prefixOffset_strictMono_band {K : ℕ → ℕ} {j₁ j₂ : ℕ}
    (h : j₁ < j₂) :
    prefixOffset K j₁ + K j₁ ≤ prefixOffset K j₂ := by
  have h1 : prefixOffset K (j₁ + 1) = prefixOffset K j₁ + K j₁ := prefixOffset_succ K j₁
  have h2 : prefixOffset K (j₁ + 1) ≤ prefixOffset K j₂ :=
    prefixOffset_mono K (by omega)
  omega

/-- Equal flattened addresses with valid within-row indices have equal row indices and equal
within-row indices. -/
theorem multiplexedIndex_injective {K : ℕ → ℕ} {j₁ j₂ k₁ k₂ : ℕ}
    (h₁ : multiplexedIndex K j₁ k₁ = multiplexedIndex K j₂ k₂)
    (hk₁ : k₁ < K j₁) (hk₂ : k₂ < K j₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · have hle := prefixOffset_strictMono_band (K := K) hlt
    unfold multiplexedIndex at h₁
    have hstep : prefixOffset K j₁ + k₁ < prefixOffset K j₂ := by omega
    omega
  · refine ⟨heq, ?_⟩
    subst heq
    unfold multiplexedIndex at h₁
    omega
  · have hle := prefixOffset_strictMono_band (K := K) hgt
    unfold multiplexedIndex at h₁
    have hstep : prefixOffset K j₂ + k₂ < prefixOffset K j₁ := by omega
    omega

/-- Every natural address below the total entry count is the flattened address of a valid table
entry. -/
theorem multiplexedIndex_surjective (J : ℕ) (K : ℕ → ℕ) :
    ∀ q, q < totalEntries J K → ∃ (j : ℕ) (k : ℕ), j < J ∧ k < K j ∧
      multiplexedIndex K j k = q := by
  induction J with
  | zero =>
    intro q hq
    simp only [totalEntries, Finset.range_zero, Finset.sum_empty] at hq
    omega
  | succ J ih =>
    intro q hq
    have hsum : totalEntries (J + 1) K = totalEntries J K + K J := by
      simp [totalEntries, Finset.sum_range_succ]
    have hq'' : q < totalEntries J K + K J := hsum ▸ hq
    by_cases hq' : q < totalEntries J K
    · obtain ⟨j, k, hj, hk, he⟩ := ih q hq'
      exact ⟨j, k, by omega, hk, he⟩
    · have hpre : prefixOffset K J = totalEntries J K := rfl
      refine ⟨J, q - prefixOffset K J, by omega, by omega, ?_⟩
      unfold multiplexedIndex
      omega

/-- XOR the data at a flattened address into the target bit vector. -/
def lookupAction {Q b : ℕ} (data : Fin Q → BitVec b) (q : Fin Q) (z : BitVec b) :
    BitVec b :=
  z ^^^ data q

/-- XOR the data at a valid row and within-row address into the target bit vector. -/
def multiplexedLookupAction {J b : ℕ} (K : ℕ → ℕ)
    (x : (j : Fin J) → Fin (K j) → BitVec b) (j : Fin J) (k : Fin (K j))
    (z : BitVec b) : BitVec b :=
  z ^^^ x j k

/-- A flat table agreeing with the ragged table at every flattened address implements the same
XOR lookup. -/
theorem lookup_chained_correct {J b : ℕ} (K : ℕ → ℕ)
    (x : (j : Fin J) → Fin (K j) → BitVec b)
    (data : Fin (totalEntries J K) → BitVec b)
    (hdata : ∀ (j : Fin J) (k : Fin (K j)),
      data (multiplexedIndexFin J K j.val k j.isLt) = x j k) :
    ∀ (j : Fin J) (k : Fin (K j)) (z : BitVec b),
      lookupAction data (multiplexedIndexFin J K j.val k j.isLt) z =
        multiplexedLookupAction K x j k z := by
  intro j k z
  simp only [lookupAction, multiplexedLookupAction, hdata]

/-- The number of valid row and within-row address pairs equals the total entry count. -/
theorem card_address_pairs (J : ℕ) (K : ℕ → ℕ) :
    Fintype.card (Σ j : Fin J, Fin (K j)) = totalEntries J K := by
  rw [Fintype.card_sigma]
  have hcard : ∀ j : Fin J, Fintype.card (Fin (K j)) = K j :=
    fun j => Fintype.card_fin (K j)
  simp only [hcard]
  rw [totalEntries]
  exact Fin.sum_univ_eq_sum_range (fun j => K j) J

/-- Counts of flat-table queries, prefix-table queries, and adders, together with the adder
width. -/
structure LookupMacroCount where

  qOracleApplications : ℕ

  jOracleApplications : ℕ

  adders : ℕ

  adderWidth : ℕ
  deriving DecidableEq, Repr

end Qatlib.Papers.QCatalysis20.MainResults
