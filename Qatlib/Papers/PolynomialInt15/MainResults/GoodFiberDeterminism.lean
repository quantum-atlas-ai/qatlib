/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolynomialInt15.MainResults.HankelRecurrence

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Finset Polynomial

/-!
# The good fibre of `Z` is a single permutation orbit

This module formalizes the algebraic core of Lemma 1 of Childs, van Dam, Hung and
Shparlinski, *Optimal quantum algorithm for polynomial interpolation*
(arXiv:1509.09271v2, Section 2.3, p. 5): if `k = d/2 + 1/2` (equivalently
`d + 1 = 2k`), then for every `z` the "good" preimage
`Z^{-1}(z)^good = Z^{-1}(z) ∩ (X_k^good × Y_k^good)` is either empty or the
simultaneous-permutation orbit of a single pair `(x, y)`, hence of size `k!`.

The paper proves this by substituting `Z(x, y) = Z(u, v)` into equation (12) and
using invertibility of a Vandermonde matrix. Here we reach the same conclusion
by the linear-recurrence route that the paper itself uses in footnote 4 and in
Section 4.1:

* two good solutions determine the same recurrence coefficients `a_j` of
  equation (47), because the Hankel matrix `H_k` is invertible (equation (48)),
  so they have the same characteristic polynomial `χ`;
* a degree-`k` polynomial has at most `k` roots, so the entries of `u` are a
  permutation of the entries of `x` (footnote 4 of the paper);
* the weights `v` are then pinned down by the invertible Vandermonde system
  (52) of the paper.

Nothing here is a weakened version of the paper's statement: the conclusion
`u = x ∘ σ`, `v = y ∘ σ` for a single permutation `σ` is exactly the sentence
"the only way to obtain a distinct `(x, y)` is to permute the indices" that
concludes the proof of Lemma 1.
-/

namespace Qatlib.Papers.PolynomialInt15.MainResults

variable {F : Type*} [Field F] {k : ℕ}

/-- For `j ≤ k` the characteristic coefficient `(-1)^j e_j` is minus the
recurrence coefficient `a_{k-j}` of equation (47). -/
theorem charCoeff_eq_neg_recCoeff (x : Fin k → F) {j : ℕ} (hj : j ≤ k) :
    charCoeff x j = -recCoeff x (k - j) := by
  simp only [recCoeff, neg_neg, show k - (k - j) = j by omega]

/-- Shared moments `z_0, …, z_{2k-1}` (equation (7) with `d + 1 = 2k`) force equal
recurrence coefficients for any good solution: the differences are annihilated by
the invertible Hankel matrix `H_k`. This is equation (49) of the paper applied to
two solutions at once. -/
theorem recCoeff_eq_of_shared_moments {x y u v : Fin k → F}
    (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hxy : ∀ j, j < 2 * k → powerSum x y j = powerSum u v j) :
    ∀ j, j < k → recCoeff x j = recCoeff u j := by
  have hinj := hankel_mulVec_injective (x := x) (y := y) hx hy
  have hzero : (hankel x y).mulVec (fun m : Fin k => recCoeff x m.val - recCoeff u m.val) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    have hn : (n : ℕ) < k := n.isLt
    have hxrec : ∑ m ∈ range k, powerSum x y ((n : ℕ) + m) * recCoeff x m
        = powerSum x y ((n : ℕ) + k) := hankel_row_recurrence x y (n : ℕ)
    have hurec : ∑ m ∈ range k, powerSum x y ((n : ℕ) + m) * recCoeff u m
        = powerSum x y ((n : ℕ) + k) := by
      have h1 : powerSum u v ((n : ℕ) + k) = powerSum x y ((n : ℕ) + k) :=
        (hxy _ (by omega)).symm
      rw [← h1, ← hankel_row_recurrence u v (n : ℕ)]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [show powerSum x y ((n : ℕ) + m) = powerSum u v ((n : ℕ) + m) from
        hxy _ (by have := Finset.mem_range.mp hm; omega)]
    simp only [Matrix.mulVec, dotProduct, hankel]
    rw [sum_fin_val_eq_sum_range
      (fun m => powerSum x y ((n : ℕ) + m) * (recCoeff x m - recCoeff u m)),
      Finset.sum_congr rfl (fun m _ => by ring : ∀ m ∈ range k,
        powerSum x y ((n : ℕ) + m) * (recCoeff x m - recCoeff u m)
          = powerSum x y ((n : ℕ) + m) * recCoeff x m
            - powerSum x y ((n : ℕ) + m) * recCoeff u m),
      Finset.sum_sub_distrib, hxrec, hurec, sub_self]
  have hδ : (fun m : Fin k => recCoeff x m.val - recCoeff u m.val) = 0 := by
    refine hinj ?_
    rw [hzero]
    simp
  intro j hj
  exact sub_eq_zero.mp (congrFun hδ ⟨j, hj⟩)

/-- Two solutions with matching recurrence coefficients have the same
characteristic polynomial `χ = ∏_i (X - x_i)` of equation (50). -/
theorem charPoly_eq_of_recCoeff_eq {x u : Fin k → F}
    (h : ∀ j, j < k → recCoeff x j = recCoeff u j) :
    (∏ i : Fin k, (X - C (x i))) = ∏ i : Fin k, (X - C (u i)) := by
  rw [prod_X_sub_C_eq_sum_charCoeff x, prod_X_sub_C_eq_sum_charCoeff u]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hc : charCoeff x j = charCoeff u j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [charCoeff_zero, charCoeff_zero]
    · rw [charCoeff_eq_neg_recCoeff x (by omega), charCoeff_eq_neg_recCoeff u (by omega),
        h (k - j) (by omega)]
  rw [hc]

/-- A degree-`k` polynomial that splits as `∏_i (X - x_i)` has all its roots
among the `x_i`; with `u` injective this exhibits `u` as a permutation of `x`.
This is footnote 4 of arXiv:1509.09271v2 ("a polynomial of degree `k` can have at
most `k` roots"). -/
theorem exists_perm_of_charPoly_eq {x u : Fin k → F}
    (h : (∏ i : Fin k, (X - C (x i))) = ∏ i : Fin k, (X - C (u i)))
    (hu : Function.Injective u) :
    ∃ σ : Equiv.Perm (Fin k), ∀ i, u i = x (σ i) := by
  have hroot : ∀ i : Fin k, ∃ s : Fin k, u i = x s := by
    intro i
    have h0 : (∏ s : Fin k, (X - C (x s))).eval (u i) = 0 := by
      rw [h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [Polynomial.eval_prod] at h0
    obtain ⟨s, -, hs⟩ := Finset.prod_eq_zero_iff.mp h0
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hs
    exact ⟨s, sub_eq_zero.mp hs⟩
  choose σ hσ using hroot
  have hσinj : Function.Injective σ := by
    intro i j hij
    refine hu ?_
    rw [hσ i, hσ j, hij]
  exact ⟨Equiv.ofBijective σ ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩, hσ⟩

/-- Lemma 1 of arXiv:1509.09271v2, "unique up to a permutation of the indices":
two good solutions with the same moments `z_0, …, z_{2k-1}` differ by a single
simultaneous permutation of `x` and `y`. -/
theorem good_solutions_eq_perm {x y u v : Fin k → F}
    (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0) (hu : Function.Injective u)
    (hxy : ∀ j, j < 2 * k → powerSum x y j = powerSum u v j) :
    ∃ σ : Equiv.Perm (Fin k), u = x ∘ σ ∧ v = y ∘ σ := by
  have hcoeff := recCoeff_eq_of_shared_moments hx hy hxy
  obtain ⟨σ, hσ⟩ := exists_perm_of_charPoly_eq (charPoly_eq_of_recCoeff_eq hcoeff) hu
  have hV : (Matrix.vandermonde u).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hu
  have hinj : Function.Injective ((Matrix.vandermonde u).transpose).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_transpose]
    exact hV
  have hw : (fun i => v i - y (σ i)) = 0 := by
    refine hinj ?_
    have hzero : ((Matrix.vandermonde u).transpose).mulVec (fun i => v i - y (σ i)) = 0 := by
      funext j
      have heq : ∑ i, (v i - y (σ i)) * u i ^ (j : ℕ) = 0 := by
        have hx' : powerSum x y (j : ℕ) = ∑ i, y (σ i) * u i ^ (j : ℕ) := by
          rw [powerSum, ← Equiv.sum_comp σ (fun s => y s * x s ^ (j : ℕ))]
          exact Finset.sum_congr rfl (fun i _ => by rw [← hσ i])
        have hu' : powerSum u v (j : ℕ) = ∑ i, v i * u i ^ (j : ℕ) := rfl
        have heq' : ∑ i, v i * u i ^ (j : ℕ) = ∑ i, y (σ i) * u i ^ (j : ℕ) := by
          rw [← hu', ← hx']
          exact (hxy (j : ℕ) (by omega)).symm
        rw [Finset.sum_congr rfl (fun i _ => sub_mul (v i) (y (σ i)) (u i ^ (j : ℕ))),
          Finset.sum_sub_distrib, heq', sub_self]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde,
        Matrix.of_apply, Pi.zero_apply]
      have hswap : (∑ i, u i ^ (j : ℕ) * (v i - y (σ i)))
          = ∑ i, (v i - y (σ i)) * u i ^ (j : ℕ) :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [hswap, heq]
    rw [hzero]
    simp
  refine ⟨σ, funext hσ, ?_⟩
  funext i
  exact sub_eq_zero.mp (congrFun hw i)

end Qatlib.Papers.PolynomialInt15.MainResults
