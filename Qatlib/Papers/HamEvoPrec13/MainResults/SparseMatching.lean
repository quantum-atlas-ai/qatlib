/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Fintype.Card

/-!
# One-sparse matrices and their off-diagonal matching

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, Lemma 1 (page 2, column 2; proof on page 3,
column 1, together with Eqs. (2)--(4)).

The paper starts its proof of Lemma 1 by observing that a real one-sparse Hamiltonian
is a direct sum of `2 × 2` blocks, each a real multiple of the Pauli matrix `σₓ`.
This file isolates the combinatorial content of that observation: every row of a
one-sparse matrix has at most one nonzero entry, so a symmetric one-sparse matrix
determines a partial matching on the index set, sending `a` to the unique column where
row `a` may be nonzero.

The main definition is `mateZero`, together with the structural lemmas that the paper
uses implicitly: the matching is involutive off its fixed points, symmetric matrices
have symmetric matching values, and entries outside the matching vanish.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.MainResults

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is one-sparse when every row contains at most one nonzero entry.

This is the sparseness notion used in Lemma 1 of the paper, restricted to the
row condition; for symmetric matrices it coincides with the usual definition in
terms of rows and columns. -/
def IsOneSparse (G : Matrix n n ℝ) : Prop :=
  ∀ a, (Finset.univ.filter fun b => G a b ≠ 0).card ≤ 1

/-- In a one-sparse matrix, two nonzero entries in the same row occupy the same column. -/
theorem IsOneSparse.column_unique {G : Matrix n n ℝ} (h : IsOneSparse G) {a b c : n}
    (hb : G a b ≠ 0) (hc : G a c ≠ 0) : b = c := by
  have hb' : b ∈ Finset.univ.filter fun d => G a d ≠ 0 := by simp [hb]
  have hc' : c ∈ Finset.univ.filter fun d => G a d ≠ 0 := by simp [hc]
  exact Finset.card_le_one_iff.mp (h a) hb' hc'

/-- The off-diagonal partner of `a` in a one-sparse matrix: the unique column `b ≠ a`
with `G a b ≠ 0`, or `a` itself when row `a` has no off-diagonal nonzero entry.

For a symmetric one-sparse matrix this is the partial matching whose `2 × 2` blocks
are the ones appearing in the proof of Lemma 1. -/
def mateZero (G : Matrix n n ℝ) (a : n) : n :=
  if h : ∃ b, b ≠ a ∧ G a b ≠ 0 then Classical.choose h else a

/-- When row `a` has an off-diagonal nonzero entry, `mateZero` selects a genuine
partner with a nonzero entry. -/
theorem mateZero_spec_of_exists {G : Matrix n n ℝ} {a : n}
    (h : ∃ b, b ≠ a ∧ G a b ≠ 0) : mateZero G a ≠ a ∧ G a (mateZero G a) ≠ 0 := by
  rw [mateZero, dif_pos h]
  exact Classical.choose_spec h

/-- When row `a` has no off-diagonal nonzero entry, `mateZero` fixes `a`. -/
theorem mateZero_eq_self_of_not_exists {G : Matrix n n ℝ} {a : n}
    (h : ¬ ∃ b, b ≠ a ∧ G a b ≠ 0) : mateZero G a = a := by
  rw [mateZero, dif_neg h]

/-- In a one-sparse matrix, any off-diagonal nonzero entry of row `a` sits exactly at
the matching partner `mateZero G a`. -/
theorem mateZero_eq_of_ne {G : Matrix n n ℝ} (h1 : IsOneSparse G) {a b : n}
    (hb : b ≠ a) (h : G a b ≠ 0) : mateZero G a = b := by
  have hex : ∃ c, c ≠ a ∧ G a c ≠ 0 := ⟨b, hb, h⟩
  have hspec := mateZero_spec_of_exists hex
  have hb' : b ∈ Finset.univ.filter fun c => G a c ≠ 0 := by simp [h]
  have hm' : mateZero G a ∈ Finset.univ.filter fun c => G a c ≠ 0 := by simp [hspec.2]
  exact Finset.card_le_one_iff.mp (h1 a) hm' hb'

/-- Row support of a one-sparse matrix: a nonzero entry is either diagonal or located
at the matching partner. -/
theorem eq_self_or_eq_mateZero {G : Matrix n n ℝ} (h1 : IsOneSparse G) {a b : n}
    (h : G a b ≠ 0) : b = a ∨ b = mateZero G a := by
  by_cases hba : b = a
  · exact Or.inl hba
  · exact Or.inr (mateZero_eq_of_ne h1 hba h).symm

/-- A one-sparse matrix vanishes off the diagonal and off the matching. -/
theorem mateZero_zero_of_ne {G : Matrix n n ℝ} (h1 : IsOneSparse G) {a b : n}
    (hb : b ≠ a) (hm : b ≠ mateZero G a) : G a b = 0 := by
  by_contra h
  rcases eq_self_or_eq_mateZero h1 h with h' | h'
  · exact hb h'
  · exact hm h'

/-- `mateZero` fixes exactly the rows without off-diagonal nonzero entries. -/
theorem mateZero_eq_self_iff {G : Matrix n n ℝ} {a : n} :
    mateZero G a = a ↔ ¬ ∃ b, b ≠ a ∧ G a b ≠ 0 := by
  constructor
  · intro h ⟨b, hb, hval⟩
    exact (mateZero_spec_of_exists ⟨b, hb, hval⟩).1 h
  · exact mateZero_eq_self_of_not_exists

/-- For a symmetric one-sparse matrix, a row with an off-diagonal entry has a vanishing
diagonal entry: otherwise the row would contain two nonzero entries. -/
theorem mateZero_diag_eq_zero {G : Matrix n n ℝ} (h1 : IsOneSparse G) {a : n}
    (ha : mateZero G a ≠ a) : G a a = 0 := by
  by_contra hdiag
  have hex : ∃ b, b ≠ a ∧ G a b ≠ 0 := by
    by_contra hne
    exact ha (mateZero_eq_self_of_not_exists hne)
  have hval : G a (mateZero G a) ≠ 0 := (mateZero_spec_of_exists hex).2
  have hdiag' : a ∈ Finset.univ.filter fun b => G a b ≠ 0 := by simp [hdiag]
  have hm' : mateZero G a ∈ Finset.univ.filter fun b => G a b ≠ 0 := by simp [hval]
  exact ha (Finset.card_le_one.mp (h1 a) a hdiag' (mateZero G a) hm').symm

/-- For a symmetric one-sparse matrix, the matching is involutive away from its fixed
points, so the `2 × 2` blocks of the paper are genuinely paired. -/
theorem mateZero_mateZero {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) {a : n}
    (ha : mateZero G a ≠ a) : mateZero G (mateZero G a) = a := by
  have hex : ∃ b, b ≠ a ∧ G a b ≠ 0 := by
    by_contra hne
    exact ha (mateZero_eq_self_of_not_exists hne)
  have hval : G a (mateZero G a) ≠ 0 := (mateZero_spec_of_exists hex).2
  have hsym : G (mateZero G a) a ≠ 0 := by
    rwa [hG.apply]
  exact mateZero_eq_of_ne h1 (Ne.symm ha) hsym

/-- The two entries of a symmetric one-sparse matrix at a matched pair agree, so the
`2 × 2` block is a symmetric block. -/
theorem mateZero_value_comm {G : Matrix n n ℝ} (hG : G.IsSymm) (a : n) :
    G (mateZero G a) a = G a (mateZero G a) :=
  hG.apply a (mateZero G a)

end Qatlib.Papers.HamEvoPrec13.MainResults
