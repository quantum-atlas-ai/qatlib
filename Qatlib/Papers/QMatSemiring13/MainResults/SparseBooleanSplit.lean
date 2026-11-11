/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatSemiring13.MainResults.MatrixProductDefs
import Mathlib.Data.Finset.Card

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — sparse Boolean product decomposition

Le Gall and Nishimura, fixed arXiv:1310.3898v1.
PDF SHA-256 1d042e95c69668deb534b7bc64dacdbeab9ccd52d8c325d88efc1728fd339971.

Section 5, proof of Theorem 5.1.  Writing `aᴿ_k`, `bᴿ_k` for the numbers of nonzero
entries in the `k`-th row of `A`, `B` and `aᶜ_k`, `bᶜ_k` for the numbers in the
`k`-th column, the paper partitions the index set `{1,...,n}` into the heavy and
light parts

`S = {k | bᴿ_k ≥ m₂/ℓ₂}`, `T = {k | aᴿ_k ≥ m₁/ℓ₁}`, `U = {k | bᶜ_k ≥ m₂/ℓ₃}`

(with `S'`, `T'`, `U'` their complements), restricts `A` and `B` to these index sets
and uses the exact identity

`A · B = A_T^S · B_S^U + A^{S'} · B_{S'} + A_{T'} · B + A · B^{U'}`

where `+` is the entry-wise OR and `M_R^C[i,j] = M[i,j] ∧ i ∈ R ∧ j ∈ C`.

This module proves that identity, and the three cardinality bounds
`|S| ≤ ℓ₂`, `|T| ≤ ℓ₁`, `|U| ≤ ℓ₃` that make the four sub-products cheaper than the
original one.  Both are unconditional combinatorial statements about Boolean
matrices; the study of the four sub-products and the resulting running time
(Theorem 5.1, Theorem 1.2) is not modelled here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMatSemiring13.MainResults

open Matrix

variable {n : ℕ}

/-- Number of nonzero entries in the `k`-th row of a Boolean matrix. -/
noncomputable def rowSupport (M : Matrix (Fin n) (Fin n) Prop) (k : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => M k j).card

/-- Number of nonzero entries in the `k`-th column of a Boolean matrix. -/
noncomputable def colSupport (M : Matrix (Fin n) (Fin n) Prop) (k : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => M i k).card

/-- Total number of nonzero entries of a Boolean matrix. -/
noncomputable def nnz (M : Matrix (Fin n) (Fin n) Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin n × Fin n => M p.1 p.2).card

/-- Double counting: the row supports sum to the total number of nonzero entries. -/
theorem sum_rowSupport_eq_nnz (M : Matrix (Fin n) (Fin n) Prop) :
    ∑ k : Fin n, rowSupport M k = nnz M := by
  classical
  have h : ∀ k : Fin n, rowSupport M k = ∑ j : Fin n, if M k j then 1 else 0 := by
    intro k
    rw [rowSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h' : nnz M = ∑ p : Fin n × Fin n, if M p.1 p.2 then 1 else 0 := by
    rw [nnz, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h', Fintype.sum_prod_type, Finset.sum_congr rfl (fun k _ => h k)]

/-- Double counting: the column supports sum to the total number of nonzero entries. -/
theorem sum_colSupport_eq_nnz (M : Matrix (Fin n) (Fin n) Prop) :
    ∑ k : Fin n, colSupport M k = nnz M := by
  classical
  have h : ∀ k : Fin n, colSupport M k = ∑ i : Fin n, if M i k then 1 else 0 := by
    intro k
    rw [colSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h' : nnz M = ∑ p : Fin n × Fin n, if M p.1 p.2 then 1 else 0 := by
    rw [nnz, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h', Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => h k)

/-- Section 5: `S = {k | bᴿ_k ≥ m/ℓ}`, written without division as `m ≤ ℓ * bᴿ_k`. -/
noncomputable def heavyRows (M : Matrix (Fin n) (Fin n) Prop) (m ℓ : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => m ≤ ℓ * rowSupport M k

/-- Section 5: `U = {k | bᶜ_k ≥ m/ℓ}`, written without division as `m ≤ ℓ * bᶜ_k`. -/
noncomputable def heavyCols (M : Matrix (Fin n) (Fin n) Prop) (m ℓ : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => m ≤ ℓ * colSupport M k

/-- Section 5: `M_R^C`, entries kept only on the row set `R` and column set `C`. -/
def restrictRC (M : Matrix (Fin n) (Fin n) Prop) (R C : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) Prop :=
  fun i j => M i j ∧ i ∈ R ∧ j ∈ C

/-- Section 5: `M_R`, the rows are restricted to `R`. -/
def restrictRows (M : Matrix (Fin n) (Fin n) Prop) (R : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) Prop :=
  fun i j => M i j ∧ i ∈ R

/-- Section 5: `M^C`, the columns are restricted to `C`. -/
def restrictCols (M : Matrix (Fin n) (Fin n) Prop) (C : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) Prop :=
  fun i j => M i j ∧ j ∈ C

/-- Theorem 5.1, proof: the four-way decomposition of the sparse Boolean product.
Every witness `k` of `A[i,k] ∧ B[k,j]` falls into one of the four cases: `k` is a
light row of `B` (second term), `i` is a light row of `A` (third term), `j` is a
light column of `B` (fourth term), or `k`, `i`, `j` are all heavy (first term). -/
theorem sparse_boolean_split (A B : Matrix (Fin n) (Fin n) Prop) (m1 m2 ℓ1 ℓ2 ℓ3 : ℕ)
    (i j : Fin n) :
    booleanProd A B i j ↔
      (booleanProd (restrictRC A (heavyRows A m1 ℓ1) (heavyRows B m2 ℓ2))
          (restrictRC B (heavyRows B m2 ℓ2) (heavyCols B m2 ℓ3)) i j ∨
        booleanProd (restrictCols A (heavyRows B m2 ℓ2)ᶜ)
          (restrictRows B (heavyRows B m2 ℓ2)ᶜ) i j ∨
        booleanProd (restrictRows A (heavyRows A m1 ℓ1)ᶜ) B i j ∨
        booleanProd A (restrictCols B (heavyCols B m2 ℓ3)ᶜ) i j) := by
  classical
  constructor
  · rintro ⟨k, hA, hB⟩
    by_cases hS : k ∈ (heavyRows B m2 ℓ2)ᶜ
    · exact Or.inr (Or.inl ⟨k, ⟨hA, hS⟩, ⟨hB, hS⟩⟩)
    · by_cases hT : i ∈ (heavyRows A m1 ℓ1)ᶜ
      · exact Or.inr (Or.inr (Or.inl ⟨k, ⟨hA, hT⟩, hB⟩))
      · by_cases hU : j ∈ (heavyCols B m2 ℓ3)ᶜ
        · exact Or.inr (Or.inr (Or.inr ⟨k, hA, ⟨hB, hU⟩⟩))
        · refine Or.inl ⟨k, ⟨hA, ?_, ?_⟩, ⟨hB, ?_, ?_⟩⟩
          · simpa using hT
          · simpa using hS
          · simpa using hS
          · simpa using hU
  · rintro (⟨k, ⟨hA, _, _⟩, ⟨hB, _, _⟩⟩ | ⟨k, ⟨hA, _⟩, ⟨hB, _⟩⟩ |
      ⟨k, ⟨hA, _⟩, hB⟩ | ⟨k, hA, ⟨hB, _⟩⟩)
    · exact ⟨k, hA, hB⟩
    · exact ⟨k, hA, hB⟩
    · exact ⟨k, hA, hB⟩
    · exact ⟨k, hA, hB⟩

/-- Section 5, first cardinality bound: a set of rows each holding at least `m/ℓ`
of the `m` nonzero entries of a matrix has at most `ℓ` elements. -/
theorem card_heavyRows_le (M : Matrix (Fin n) (Fin n) Prop) (m ℓ : ℕ) (hm : 0 < m)
    (hnnz : nnz M = m) : (heavyRows M m ℓ).card ≤ ℓ := by
  classical
  set S := heavyRows M m ℓ with hS
  have hmem : ∀ k ∈ S, m ≤ ℓ * rowSupport M k := by
    intro k hk
    simpa [hS, heavyRows] using hk
  have hc : S.card * m = ∑ _k ∈ S, m := by
    rw [Finset.sum_const]
    simp
  have h₁ : S.card * m ≤ ℓ * ∑ k ∈ S, rowSupport M k := by
    rw [hc, Finset.mul_sum]
    exact Finset.sum_le_sum hmem
  have h₂ : ∑ k ∈ S, rowSupport M k ≤ m := by
    rw [← hnnz, ← sum_rowSupport_eq_nnz M]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => Nat.zero_le _)
  have h₃ : S.card * m ≤ ℓ * m := by
    refine h₁.trans (Nat.mul_le_mul_left ℓ h₂)
  exact Nat.le_of_mul_le_mul_right h₃ hm

/-- Section 5, second cardinality bound (columns of `B`). -/
theorem card_heavyCols_le (M : Matrix (Fin n) (Fin n) Prop) (m ℓ : ℕ) (hm : 0 < m)
    (hnnz : nnz M = m) : (heavyCols M m ℓ).card ≤ ℓ := by
  classical
  set U := heavyCols M m ℓ with hU
  have hmem : ∀ k ∈ U, m ≤ ℓ * colSupport M k := by
    intro k hk
    simpa [hU, heavyCols] using hk
  have hc : U.card * m = ∑ _k ∈ U, m := by
    rw [Finset.sum_const]
    simp
  have h₁ : U.card * m ≤ ℓ * ∑ k ∈ U, colSupport M k := by
    rw [hc, Finset.mul_sum]
    exact Finset.sum_le_sum hmem
  have h₂ : ∑ k ∈ U, colSupport M k ≤ m := by
    rw [← hnnz, ← sum_colSupport_eq_nnz M]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      (fun _ _ _ => Nat.zero_le _)
  have h₃ : U.card * m ≤ ℓ * m := h₁.trans (Nat.mul_le_mul_left ℓ h₂)
  exact Nat.le_of_mul_le_mul_right h₃ hm

end Qatlib.Papers.QMatSemiring13.MainResults
