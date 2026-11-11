/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolynomialInt15.MainResults.GoodFiberDeterminism

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Polynomial

/-!
# Lemma 1: the good fibre of `Z` has `0` or `k!` elements

This module completes Lemma 1 of Childs, van Dam, Hung and Shparlinski,
*Optimal quantum algorithm for polynomial interpolation* (arXiv:1509.09271v2,
Section 2.3, p. 5).

For `k = d/2 + 1/2` (equivalently `d + 1 = 2k`) and `z ∈ F_q^{d+1}`, the good
preimage

  `Z^{-1}(z)^good = {(x, y) ∈ F_q^k × F_q^k : Z(x, y) = z, x_i ≠ x_j for i ≠ j, y_i ≠ 0}`

is either empty or has exactly `k!` elements.

The paper's proof shows that the good solutions are unique up to a permutation of
the indices and then counts the `k!` permutations. `GoodFiberDeterminism` supplies
the uniqueness-up-to-permutation step (`good_solutions_eq_perm`, using footnote 4
of the paper); here we package it as a bijection between `Equiv.Perm (Fin k)` and
the fibre, which gives the count.
-/

namespace Qatlib.Papers.PolynomialInt15.MainResults

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

/-- The "good" preimage `Z^{-1}(z)^good` of Lemma 1: pairs `(x, y)` with `x` having
pairwise distinct entries (`x ∈ X_k^good`), `y` having nonzero entries
(`y ∈ Y_k^good`), and `Z(x, y) = z` on the `d + 1 = 2k` coordinates. -/
abbrev GoodFiber (z : Fin (2 * k) → F) : Type _ :=
  { p : (Fin k → F) × (Fin k → F) //
      (∀ j : Fin (2 * k), powerSum p.1 p.2 (j : ℕ) = z j) ∧
        Function.Injective p.1 ∧ ∀ i, p.2 i ≠ 0 }

omit [Fintype F] [DecidableEq F] in
/-- The components `Z(x, y)_j` are invariant under a simultaneous permutation of
the points and their weights, as used in the paper's phrase "the only way to
obtain a distinct `(x, y)` is to permute the indices". -/
theorem powerSum_perm (x y : Fin k → F) (σ : Equiv.Perm (Fin k)) (j : ℕ) :
    powerSum (fun i => x (σ i)) (fun i => y (σ i)) j = powerSum x y j := by
  rw [powerSum, powerSum, ← Equiv.sum_comp σ (fun s => y s * x s ^ j)]

/-- Lemma 1 of arXiv:1509.09271v2: with `d + 1 = 2k`, the good preimage of any
`z` has either `0` or exactly `k!` elements. -/
theorem goodFiber_card (z : Fin (2 * k) → F) :
    Fintype.card (GoodFiber z) = 0 ∨ Fintype.card (GoodFiber z) = Nat.factorial k := by
  by_cases hempty : IsEmpty (GoodFiber z)
  · exact Or.inl (Fintype.card_eq_zero_iff.mpr hempty)
  · obtain ⟨⟨x, y⟩, hz, hx, hy⟩ := not_isEmpty_iff.mp hempty
    let toFun : Equiv.Perm (Fin k) → GoodFiber z := fun σ =>
      ⟨(fun i => x (σ i), fun i => y (σ i)),
        fun j => by rw [powerSum_perm x y σ (j : ℕ)]; exact hz j,
        fun a b hab => σ.injective (hx hab),
        fun i => hy (σ i)⟩
    have toFun_val : ∀ σ, (toFun σ).1 = (fun i => x (σ i), fun i => y (σ i)) := fun _ => rfl
    have hinj : Function.Injective toFun := by
      intro σ τ h
      have h' : (toFun σ).1 = (toFun τ).1 := by rw [h]
      rw [toFun_val, toFun_val] at h'
      have h1 : (fun i => x (σ i)) = (fun i => x (τ i)) := congrArg Prod.fst h'
      exact Equiv.ext (fun i => hx (congrFun h1 i))
    have hsurj : Function.Surjective toFun := by
      rintro ⟨⟨u, v⟩, huz, hu, hv⟩
      have hxy : ∀ j, j < 2 * k → powerSum x y j = powerSum u v j := by
        intro j hj
        rw [hz ⟨j, hj⟩, huz ⟨j, hj⟩]
      obtain ⟨σ, hσ1, hσ2⟩ := good_solutions_eq_perm hx hy hu hxy
      refine ⟨σ, Subtype.ext ?_⟩
      rw [toFun_val]
      exact Prod.ext hσ1.symm hσ2.symm
    have hcard : Fintype.card (GoodFiber z) = Fintype.card (Equiv.Perm (Fin k)) :=
      (Fintype.card_of_bijective (f := toFun) ⟨hinj, hsurj⟩).symm
    exact Or.inr (by rw [hcard, Fintype.card_perm, Fintype.card_fin])

end Qatlib.Papers.PolynomialInt15.MainResults
