/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatSemiring13.MainResults.MatrixProductDefs

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — dominance-product reduction for the `(max, min)`-product

Le Gall and Nishimura, fixed arXiv:1310.3898v1.
PDF SHA-256 1d042e95c69668deb534b7bc64dacdbeab9ccd52d8c325d88efc1728fd339971.

Section 2 of the paper observes that computing the `(max,min)`-product reduces to
computing the product `⊳` of Definition 2.1:

`C[i,j] = max ((A ⊳ B)[i,j], (Bᵀ ⊳ Aᵀ)[j,i])`.

This module proves that identity together with the correctness facts that the
paper's algorithms read off the definitions:
* with `A` free of `-∞` entries, `(A ⊳ B)[i,j] = -∞` exactly when `A[i,k] > B[k,j]`
  for every `k`, which is the first clause of Definition 2.1;
* in the same setting `(A ∗ B)[i,j] = 1` exactly when `(A ⊳ B)[i,j] ≠ -∞`;
* for `u = v = 1` the generalized existence dominance product of Definition 3.1 is
  the ordinary existence dominance product.

Boundary: the paper's assertion that this reduction is "easy to check" is what is
formalized; the running-time consequences (Theorem 1.1, Theorem 4.1) are not
modelled here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMatSemiring13.MainResults

open Matrix

/-- Definition 2.1, first clause: for `A` over `ℤ ∪ {∞}`, the entry
`(A ⊳ B)[i,j]` is `-∞` exactly when `A[i,k] > B[k,j]` for every `k`.  The hypothesis
`hA` rules out `-∞` entries in `A`, which is the paper's carrier for the left
factor. -/
theorem dominance_eq_bot_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) Val)
    (hA : ∀ i k, A i k ≠ ⊥) (i j : Fin n) :
    dominance A B i j = ⊥ ↔ ∀ k : Fin n, B k j < A i k := by
  rw [dominance, Finset.sup_eq_bot_iff]
  constructor
  · intro h k
    by_contra hk
    have hle : A i k ≤ B k j := le_of_not_gt hk
    have hterm : (if A i k ≤ B k j then A i k else ⊥) = A i k := if_pos hle
    have hbot : (if A i k ≤ B k j then A i k else ⊥) = ⊥ := h k (Finset.mem_univ k)
    rw [hterm] at hbot
    exact hA i k hbot
  · intro h k _
    have hlt : ¬ (A i k ≤ B k j) := not_le.mpr (h k)
    exact if_neg hlt

/-- With `A` free of `-∞` entries, `(A ∗ B)[i,j] = 1` exactly when `A ⊳ B` has a
finite entry at `(i,j)`. -/
theorem dominance_ne_bot_iff_existsDominance {n : ℕ} (A B : Matrix (Fin n) (Fin n) Val)
    (hA : ∀ i k, A i k ≠ ⊥) (i j : Fin n) :
    dominance A B i j ≠ ⊥ ↔ existsDominance A B i j := by
  constructor
  · intro hne
    by_contra h
    exact hne ((dominance_eq_bot_iff A B hA i j).mpr
      (fun k => not_le.mp (fun hk => h ⟨k, hk⟩)))
  · rintro ⟨k, hk⟩ hbot
    exact absurd hk (not_le.mpr ((dominance_eq_bot_iff A B hA i j).mp hbot k))

/-- Section 2: the `(max, min)`-product is computed from two products `⊳`, namely

`C[i,j] = max ((A ⊳ B)[i,j], (Bᵀ ⊳ Aᵀ)[j,i])`.

Terms with `A[i,k] ≤ B[k,j]` contribute `A[i,k]` and are collected by `A ⊳ B`;
terms with `B[k,j] < A[i,k]` contribute `B[k,j]` and are collected by `Bᵀ ⊳ Aᵀ`. -/
theorem maxMinProd_eq_max_dominance {n : ℕ} (A B : Matrix (Fin n) (Fin n) Val) :
    maxMinProd A B = fun i j => max (dominance A B i j) (dominance Bᵀ Aᵀ j i) := by
  funext i j
  have h₁ : dominance A B i j
      = (Finset.univ : Finset (Fin n)).sup (fun k => if A i k ≤ B k j then A i k else ⊥) :=
    rfl
  have h₂ : dominance Bᵀ Aᵀ j i
      = (Finset.univ : Finset (Fin n)).sup (fun k => if B k j ≤ A i k then B k j else ⊥) := by
    simp [dominance]
  rw [maxMinProd, h₁, h₂]
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun k _ => ?_)
    by_cases h : A i k ≤ B k j
    · have hmin : min (A i k) (B k j) = A i k := min_eq_left h
      rw [hmin]
      refine le_trans ?_ (le_max_left _ _)
      simpa [h] using Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
        (f := fun k => if A i k ≤ B k j then A i k else ⊥) (Finset.mem_univ k)
    · have hlt : B k j < A i k := lt_of_not_ge h
      have hmin : min (A i k) (B k j) = B k j := min_eq_right (le_of_lt hlt)
      rw [hmin]
      refine le_trans ?_ (le_max_right _ _)
      simpa [le_of_lt hlt] using Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
        (f := fun k => if B k j ≤ A i k then B k j else ⊥) (Finset.mem_univ k)
  · refine max_le ?_ ?_
    · refine Finset.sup_le (fun k _ => ?_)
      by_cases h : A i k ≤ B k j
      · rw [if_pos h]
        have hmin : min (A i k) (B k j) = A i k := min_eq_left h
        rw [← hmin]
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun k => min (A i k) (B k j)) (Finset.mem_univ k)
      · rw [if_neg h]
        exact bot_le
    · refine Finset.sup_le (fun k _ => ?_)
      by_cases h : B k j ≤ A i k
      · rw [if_pos h]
        have hmin : min (A i k) (B k j) = B k j := min_eq_right h
        rw [← hmin]
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun k => min (A i k) (B k j)) (Finset.mem_univ k)
      · rw [if_neg h]
        exact bot_le

/-- Definition 3.1, consistency clause: for `u = v = 1` the generalized existence
dominance product is the ordinary one, its value being `(1,1)` when `A ∗ B` has a
nonzero entry and `(0,0)` otherwise. -/
theorem generalizedDominance_fin_one_iff {n : ℕ}
    (A : Fin 1 → Matrix (Fin n) (Fin n) Val) (B : Fin 1 → Matrix (Fin n) (Fin n) Val)
    (i j : Fin n) :
    generalizedDominance A B i j ≠ ⊥ ↔ existsDominance (A 0) (B 0) i j := by
  classical
  have huniv : (Finset.univ : Finset (Fin 1 × Fin 1)) = {(0, 0)} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  rw [generalizedDominance, huniv, Finset.sup_singleton]
  by_cases h : existsDominance (A 0) (B 0) i j
  · simp [h]
  · simp [h]

end Qatlib.Papers.QMatSemiring13.MainResults
