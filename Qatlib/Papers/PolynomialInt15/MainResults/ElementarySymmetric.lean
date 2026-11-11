/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Elementary symmetric functions and Newton's identity

This module formalizes Lemma 5 of Childs, van Dam, Hung and Shparlinski,
*Optimal quantum algorithm for polynomial interpolation* (arXiv:1509.09271v2,
Section 4.1, equation (37)), together with the elementary symmetric functions
`e_j` of equation (36).

For `k` elements `x 0, …, x (k-1)` of a commutative ring, equation (36) defines

  `e_j(x_1, …, x_k) = ∑_{1 ≤ i_1 < ⋯ < i_j ≤ k} x_{i_1} ⋯ x_{i_j}`,

which is `esymm x j` below. Lemma 5 (equation (37)) says that every `x i` is a
root of the monic polynomial whose coefficients are `(-1)^j e_j`, namely

  `x_i^k = -∑_{j=1}^{k} x_i^{k-j} (-1)^j e_j`.

We record the paper's form together with the characteristic-polynomial form
`x_i^k = -∑_{j<k} (-1)^{k-j} e_{k-j} x_i^j` that Lemma 6 and the Prony-style
inversion of `Z` in the proof of Theorem 3 use.

The paper proves Lemma 5 by induction on `k`; here we expand
`∏_i (X - x_i)` with Vieta's formulas (`Multiset.prod_X_sub_X_eq_sum_esymm`),
which is the same algebraic identity the induction establishes, and evaluate at
the root `x i`. This is stated over an arbitrary commutative ring, so it applies
to `ZMod q` for prime powers `q` as needed by the paper.
-/

namespace Qatlib.Papers.PolynomialInt15.MainResults

open Finset Polynomial

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The `j`-th elementary symmetric function of `x 0, …, x (k-1)`, i.e. equation
(36) of arXiv:1509.09271v2: the sum of all products of `j` distinct entries. -/
noncomputable def esymm (x : Fin k → R) (j : ℕ) : R :=
  ∑ t ∈ (univ : Finset (Fin k)).powersetCard j, t.prod x

/-- The coefficient `(-1)^j e_j` of `X^{k-j}` in the characteristic polynomial
`∏_i (X - x_i)`; it is minus the recurrence coefficient `a_j` of the paper's
equation (47). -/
noncomputable def charCoeff (x : Fin k → R) (j : ℕ) : R := (-1 : R) ^ j * esymm x j

/-- The zeroth elementary symmetric function is `1`. -/
@[simp] theorem esymm_zero (x : Fin k → R) : esymm x 0 = 1 := by
  have h : (univ : Finset (Fin k)).powersetCard 0 = {∅} := by simp
  simp [esymm, h]

/-- The `j`-th elementary symmetric function vanishes when `j > k`. -/
theorem esymm_eq_zero_of_lt (x : Fin k → R) {j : ℕ} (hj : k < j) : esymm x j = 0 := by
  have h : (univ : Finset (Fin k)).powersetCard j = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    simpa using hj
  simp [esymm, h]

/-- The `k`-th elementary symmetric function is the product of all entries. -/
theorem esymm_self (x : Fin k → R) : esymm x k = ∏ i, x i := by
  have h : (univ : Finset (Fin k)).powersetCard k = {univ} := by
    have h' := Finset.powersetCard_self (univ : Finset (Fin k))
    rw [Finset.card_univ, Fintype.card_fin] at h'
    exact h'
  simp [esymm, h]

/-- The constant coefficient of the characteristic polynomial is `1`. -/
theorem charCoeff_zero (x : Fin k → R) : charCoeff x 0 = 1 := by
  simp [charCoeff]

/-- Vieta's expansion of the characteristic polynomial of `x` with the elementary
symmetric functions of equation (36): `∏_i (X - x_i) = ∑_j (-1)^j e_j X^{k-j}`.
This is the identity the paper's induction on `k` establishes in the proof of
Lemma 5. -/
theorem prod_X_sub_C_eq_sum_charCoeff (x : Fin k → R) :
    (∏ i : Fin k, (X - C (x i))) =
      ∑ j ∈ range (k + 1), C (charCoeff x j) * X ^ (k - j) := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm ((univ : Finset (Fin k)).val.map x)
  have hcard : (Multiset.map x (univ : Finset (Fin k)).val).card = k := by simp
  rw [hcard] at h
  have hL : (∏ i : Fin k, (X - C (x i)))
      = (Multiset.map (fun t => X - C t)
          ((univ : Finset (Fin k)).val.map x)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hL, h]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Finset.esymm_map_val]
  rw [show (-1 : R[X]) = C (-1 : R) by simp, ← map_pow, ← mul_assoc, ← C_mul]
  rfl

/-- Every entry `x i` is a root of the characteristic polynomial `∏_a (X - x_a)`. -/
theorem eval_prod_X_sub_C (x : Fin k → R) (i : Fin k) :
    (∏ a : Fin k, (X - C (x a))).eval (x i) = 0 := by
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Evaluating the Vieta expansion at the root `x i` gives the linear relation
`∑_j (-1)^j e_j (x i)^{k-j} = 0`. -/
theorem eval_prod_X_sub_C_eq_sum (x : Fin k → R) (i : Fin k) :
    (∑ j ∈ range (k + 1), charCoeff x j * x i ^ (k - j)) = 0 := by
  rw [← eval_prod_X_sub_C x i, prod_X_sub_C_eq_sum_charCoeff, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp

/-- Lemma 5 in the indexed form produced by splitting the `j = 0` term of the
Vieta expansion: `x_i^k = -∑_{j<k} (-1)^{j+1} e_{j+1} x_i^{k-j-1}`. -/
theorem newton_identity_range (x : Fin k → R) (i : Fin k) :
    x i ^ k = - ∑ j ∈ range k, charCoeff x (j + 1) * x i ^ (k - (j + 1)) := by
  have h0 := eval_prod_X_sub_C_eq_sum x i
  rw [Finset.sum_range_succ'] at h0
  rw [show charCoeff x 0 * x i ^ (k - 0) = x i ^ k by simp [charCoeff]] at h0
  exact eq_neg_of_add_eq_zero_right h0

/-- Lemma 5 in characteristic-polynomial form, ready for the linear recurrence of
Lemma 6: `x_i^k = -∑_{j<k} (-1)^{k-j} e_{k-j} x_i^j`. -/
theorem newton_identity_charPoly (x : Fin k → R) (i : Fin k) :
    x i ^ k = - ∑ j ∈ range k, charCoeff x (k - j) * x i ^ j := by
  rw [newton_identity_range x i, ← Finset.sum_range_reflect
    (fun j => charCoeff x (j + 1) * x i ^ (k - (j + 1))) k]
  refine congrArg Neg.neg (Finset.sum_congr rfl ?_)
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : k - 1 - j + 1 = k - j := by omega
  have h2 : k - (k - j) = j := by omega
  rw [h1, h2]

/-- Reindexing identity turning a sum over `{1, …, k}` into a sum over
`{0, …, k-1}`; used to write equation (37) of the paper in indexed form. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, f j = ∑ j ∈ range k, f (j + 1) := by
  refine Finset.sum_nbij' (fun a => a - 1) (fun b => b + 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha
    beta_reduce
    rw [Finset.mem_range]
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    beta_reduce
    rw [Finset.mem_Icc]
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    beta_reduce
    omega
  · intro b _
    beta_reduce
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    beta_reduce
    have h : a - 1 + 1 = a := by omega
    rw [h]

/-- Lemma 5 of arXiv:1509.09271v2, equation (37), literally: for every
`i ∈ {1, …, k}` we have `x_i^k = -∑_{j=1}^{k} x_i^{k-j} (-1)^j e_j`. -/
theorem newton_identity (x : Fin k → R) (i : Fin k) :
    x i ^ k =
      - ∑ j ∈ Finset.Icc 1 k, x i ^ (k - j) * charCoeff x j := by
  rw [newton_identity_range x i, ← sum_Icc_one_eq_sum_range
    (fun j => charCoeff x j * x i ^ (k - j)) k]
  refine congrArg Neg.neg (Finset.sum_congr rfl ?_)
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [mul_comm]

end Qatlib.Papers.PolynomialInt15.MainResults
