/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Finite chains and product operators

This module defines finite real vector operations, product-chain matrices, and the predicates
`SpectralGapAtLeast` and `SpectralGapEquals` for the spectral analysis used in [Tani2009]. The
lower-bound predicate records stochasticity, symmetry, and squared-norm contraction on vectors
whose entries sum to zero.

## Main statements

* `act_const` and `sum_act`: preservation of constants and coordinate sums.
* `chainProduct`: the matrix for independent transitions on a product.
* `sqNorm_add_of_dot_zero`: orthogonal decomposition of squared norms.

## References

* [Tani, 2009][Tani2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

/-- The sum of the squares of the coordinates of a finite real vector. -/
def sqNorm {I : Type*} [Fintype I] (v : I → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- The finite real dot product, defined as the sum of coordinatewise products. -/
def dot {I : Type*} [Fintype I] (u v : I → ℝ) : ℝ := ∑ i, u i * v i

/-- A transition matrix is symmetric and contracts the squared norm of every vector whose
entries sum to zero by at most `(1-δ)^2`. -/
def SpectralGapAtLeast {I : Type*} [Fintype I] (P : I → I → ℝ) (δ : ℝ) : Prop :=
  IsTransitionMatrix P ∧ (∀ i j, P i j = P j i) ∧
    ∀ v : I → ℝ, (∑ i, v i) = 0 → sqNorm (fun i => ∑ j, P i j * v j) ≤ (1 - δ) ^ 2 * sqNorm v

/-- The action of a finite real matrix on a vector by summing each row against the vector. -/
def act {I : Type*} [Fintype I] (P : I → I → ℝ) (v : I → ℝ) : I → ℝ :=
  fun i => ∑ j, P i j * v j

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The product-chain matrix on pairs, whose entries are products of the corresponding entries
of the two factor matrices. -/
def chainProduct (P : I → I → ℝ) (Q : J → J → ℝ) : (I × J) → (I × J) → ℝ :=
  fun p q => P p.1 q.1 * Q p.2 q.2

/-- The predicate `SpectralGapAtLeast P δ` holds, and every parameter satisfying
`SpectralGapAtLeast P` is at most `δ`. -/
def SpectralGapEquals {I : Type*} [Fintype I] (P : I → I → ℝ) (δ : ℝ) : Prop :=
  SpectralGapAtLeast P δ ∧ ∀ δ', SpectralGapAtLeast P δ' → δ' ≤ δ

/-- A matrix whose row sums are one fixes every constant vector. -/
theorem act_const {P : I → I → ℝ} (hP : ∀ i, ∑ j, P i j = 1) (c : ℝ) :
    act P (fun _ => c) = fun _ => c := by
  funext i
  simp only [act]
  rw [← Finset.sum_mul, hP i, one_mul]

/-- A matrix whose column sums are one preserves the sum of a vector's entries. -/
theorem sum_act {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1)
    (v : I → ℝ) : ∑ i, act P v i = ∑ i, v i := by
  simp only [act]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, P i j * v j = ∑ j, (∑ i, P i j) * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      _ = ∑ j, v j := by simp [hc]

/-- A matrix whose column sums are one maps a vector whose entries sum to zero to another such
vector. -/
theorem sum_act_zero {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1) {v : I → ℝ}
    (hv : ∑ i, v i = 0) : ∑ i, act P v i = 0 := by
  rw [sum_act hc v, hv]

/-- Matrix action preserves addition of vectors. -/
theorem act_add (P : I → I → ℝ) (u v : I → ℝ) :
    act P (u + v) = act P u + act P v := by
  funext i
  simp only [act, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Matrix action preserves subtraction of vectors. -/
theorem act_sub (P : I → I → ℝ) (u v : I → ℝ) :
    act P (u - v) = act P u - act P v := by
  funext i
  simp only [act, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The entries of `act P v` sum to zero if the columns of `P` sum to one and the entries of `v`
sum to zero. -/
theorem act_zeroSum {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1)
    {v : I → ℝ} (hv : ∑ i, v i = 0) : (∑ i, act P v i) = 0 :=
  sum_act_zero hc hv

/-- A vector whose entries sum to zero is orthogonal to the constant vector with value one. -/
theorem dot_one_zero {v : I → ℝ} (hv : ∑ i, v i = 0) :
    dot (fun _ : I => (1 : ℝ)) v = 0 := by
  simp only [dot, one_mul, hv]

/-- Functions on a product depending on separate coordinates are orthogonal when the function of
the second coordinate sums to zero. -/
theorem dot_prod_split {a : I → ℝ} {b : J → ℝ} (hb : ∑ j, b j = 0) :
    dot (fun p : I × J => a p.1) (fun p : I × J => b p.2) = 0 := by
  simp only [dot, Fintype.sum_prod_type, ← Finset.mul_sum, hb, mul_zero,
    Finset.sum_const_zero]

/-- Lifting a vector to a product through the second coordinate multiplies its squared norm by
the cardinality of the first factor. -/
theorem sqNorm_prod_right {c : J → ℝ} :
    sqNorm (fun p : I × J => c p.2) = (Fintype.card I : ℝ) * sqNorm c := by
  simp only [sqNorm, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- Lifting a vector to a product through the first coordinate multiplies its squared norm by
the cardinality of the second factor. -/
theorem sqNorm_prod_left {a : I → ℝ} :
    sqNorm (fun p : I × J => a p.1) = (Fintype.card J : ℝ) * sqNorm a := by
  simp only [sqNorm, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]

/-- The squared norm of a sum of orthogonal vectors is the sum of their squared norms. -/
theorem sqNorm_add_of_dot_zero {u v : I → ℝ} (h : dot u v = 0) :
    sqNorm (u + v) = sqNorm u + sqNorm v := by
  have h1 : sqNorm (u + v) = ∑ i, (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  have hd : ∑ i, u i * v i = 0 := h
  rw [h1]
  simp only [sqNorm, Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_zero]
  ring

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
