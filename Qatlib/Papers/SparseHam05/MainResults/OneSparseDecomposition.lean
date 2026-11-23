/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseHam05.MainResults.Defs

/-!
# One-sparse decomposition by matching support indices

In the setting of [BerryEtAl2007Sparse], Lemma 2, the finite
support of a Hermitian column-sparse matrix is also row-sparse.
Color each entry by its indices in the row and column support. This
gives a one-sparse decomposition without a query complexity bound
or a Hermiticity requirement on the summands.
[Fixed source](https://arxiv.org/abs/quant-ph/0508139v2).
-/

@[expose] public section

open Matrix
open Qatlib.Papers.SparseHam05.MainResults
open scoped Classical BigOperators

namespace Qatlib.Papers.SparseHam05.MainResults

/-- A Hermitian matrix with at most `d` nonzero entries in each column is
a sum of `d²` matrices with at most one nonzero entry per row and column. -/
theorem one_sparse_decomposition_of_hermitian
    (N d : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hsp : ColSparse d H)
    (hherm : Hᴴ = H) :
    ∃ Hs : Fin (d ^ 2) → Matrix (Fin N) (Fin N) ℂ,
      IsSparseDecomposition H (d ^ 2) Hs := by
  classical
  have hr : ∀ i, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤ d := by
    intro i
    convert hsp i using 1
    congr 1
    ext j
    have he : star (H j i) = H i j := congrFun (congrFun hherm i) j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← he, star_ne_zero]
  let R : ∀ i, {j // H i j ≠ 0} ↪ Fin d := fun i =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_subtype, Fintype.card_fin] using hr i))
  let C : ∀ j, {i // H i j ≠ 0} ↪ Fin d := fun j =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_subtype, Fintype.card_fin] using hsp j))
  let e : (Fin d × Fin d) ↪ Fin (d ^ 2) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [pow_two]))
  let color (i j : Fin N) (h : H i j ≠ 0) : Fin (d ^ 2) :=
    e (R i ⟨j, h⟩, C j ⟨i, h⟩)
  let Hs (k : Fin (d ^ 2)) : Matrix (Fin N) (Fin N) ℂ :=
    fun i j => if h : H i j ≠ 0 then if color i j h = k then H i j else 0 else 0
  have hsupp (k : Fin (d ^ 2)) (i j : Fin N) (h : Hs k i j ≠ 0) :
      ∃ hij : H i j ≠ 0, color i j hij = k := by
    by_cases hij : H i j ≠ 0
    · refine ⟨hij, ?_⟩
      by_contra hc
      simp [Hs, hij, hc] at h
    · simp [Hs, hij] at h
  refine ⟨Hs, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    rw [Matrix.sum_apply]
    by_cases hij : H i j ≠ 0
    · symm
      rw [Finset.sum_eq_single (color i j hij)]
      · simp [Hs, hij]
      · intro b _ hb
        simp [Hs, hij, Ne.symm hb]
      · simp
    · simp [Hs]
  · intro k
    constructor
    · intro i
      apply Finset.card_le_one.mpr
      intro j hj l hl
      obtain ⟨hij, hjc⟩ := hsupp k i j (Finset.mem_filter.mp hj).2
      obtain ⟨hil, hlc⟩ := hsupp k i l (Finset.mem_filter.mp hl).2
      have heq := e.injective (hjc.trans hlc.symm)
      exact congrArg Subtype.val ((R i).injective (congrArg Prod.fst heq))
    · intro j
      apply Finset.card_le_one.mpr
      intro i hi l hl
      obtain ⟨hij, hic⟩ := hsupp k i j (Finset.mem_filter.mp hi).2
      obtain ⟨hlj, hlc⟩ := hsupp k l j (Finset.mem_filter.mp hl).2
      have heq := e.injective (hic.trans hlc.symm)
      exact congrArg Subtype.val ((C j).injective (congrArg Prod.snd heq))

end Qatlib.Papers.SparseHam05.MainResults
