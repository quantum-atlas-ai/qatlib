/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolynomialInt15.MainResults.PowerSumRecurrence
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Finset

/-!
# The Hankel form of the recurrence (equations (47)–(49))

This module formalizes the linear-algebraic step at the start of the proof of
Theorem 3 in Childs, van Dam, Hung and Shparlinski, *Optimal quantum algorithm
for polynomial interpolation* (arXiv:1509.09271v2, Section 4.1).

Equation (47) writes the recurrence of Lemma 6 as the Hankel system

  `H_k a = (z_k, z_{k+1}, …, z_{2k-1})`,  `(H_k)_{ij} = z_{i+j}`,

with `a_j = -(-1)^{k-j} e_{k-j}`. Equation (48) factors

  `H_k = V_kᵀ · diag(y) · V_k`,  `(V_k)_{ij} = x_i^j`,

which is invertible whenever the `x_i` are pairwise distinct and all `y_i` are
nonzero — the "good" hypotheses `x ∈ X_k^good`, `y ∈ Y_k^good` of the paper.
Equation (49) then says that the coefficients `a` are uniquely determined by
`z` alone, which is what lets the paper compute `Z^{-1}(z)` efficiently by
solving a linear system and factoring a degree-`k` polynomial.
-/

namespace Qatlib.Papers.PolynomialInt15.MainResults

variable {F : Type*} [Field F] {k : ℕ}

/-- The Hankel moment matrix `H_k` of equation (47): `(H_k)_{ij} = z_{i+j}`. -/
noncomputable def hankel (x y : Fin k → F) : Matrix (Fin k) (Fin k) F :=
  fun i j => powerSum x y (i.val + j.val)

/-- Row `i` of the product `V_kᵀ · diag(y)`, as used in equation (48):
`(V_kᵀ diag(y))_{it} = x_t^i y_t`. -/
theorem vandermonde_transpose_mul_diagonal (x y : Fin k → F) (i t : Fin k) :
    ((Matrix.vandermonde x).transpose * Matrix.diagonal y) i t = x t ^ (i : ℕ) * y t := by
  rw [Matrix.mul_apply, Finset.sum_eq_single t]
  · simp [Matrix.vandermonde]
  · intro s _ hst
    simp [hst]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- Equation (48) of arXiv:1509.09271v2: the Hankel matrix factors as
`H_k = V_kᵀ · diag(y) · V_k`, i.e. `(H_k)_{ij} = ∑_t x_t^i y_t x_t^j`. -/
theorem hankel_eq_vandermonde (x y : Fin k → F) :
    hankel x y
      = (Matrix.vandermonde x).transpose * Matrix.diagonal y * Matrix.vandermonde x := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [vandermonde_transpose_mul_diagonal]
  simp only [Matrix.vandermonde, hankel, powerSum]
  refine Finset.sum_congr rfl ?_
  intro t _
  simp only [Matrix.of_apply]
  rw [pow_add]
  ring

/-- For distinct `x i` and nonzero `y i` the Hankel matrix `H_k` is invertible;
this is the determinant consequence `det H_k = det(V_k)^2 · ∏_i y_i ≠ 0` of the
factorization (48) used in equation (49). -/
theorem hankel_det_ne_zero (x y : Fin k → F) (hx : Function.Injective x)
    (hy : ∀ i, y i ≠ 0) : (hankel x y).det ≠ 0 := by
  rw [hankel_eq_vandermonde, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hy' : (∏ i, y i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)
  exact mul_ne_zero (mul_ne_zero hV hy') hV

/-- Equation (49): under the goodness hypotheses of the paper, the linear system
`H_k a = z_{[k..2k-1]}` has at most one solution. -/
theorem hankel_mulVec_injective (x y : Fin k → F) (hx : Function.Injective x)
    (hy : ∀ i, y i ≠ 0) : Function.Injective (hankel x y).mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact hankel_det_ne_zero x y hx hy

/-- Bridge between the `Fin k` sum of `Matrix.mulVec` and the `range k` sums of
the recurrence: `∑ j : Fin k, f j.val = ∑ j ∈ range k, f j`. -/
theorem sum_fin_val_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ j : Fin k, f j.val = ∑ j ∈ range k, f j := by
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [dif_pos (Finset.mem_range.mp hj)]

/-- Equation (47) of arXiv:1509.09271v2 in matrix form: the recurrence
coefficients `a_j = -(-1)^{k-j} e_{k-j}` solve the Hankel system. -/
theorem hankel_mulVec_recCoeff (x y : Fin k → F) :
    (hankel x y).mulVec (fun j => recCoeff x j.val)
      = fun i => powerSum x y (i.val + k) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, hankel]
  rw [sum_fin_val_eq_sum_range (fun j => powerSum x y (i.val + j) * recCoeff x j)]
  exact hankel_row_recurrence x y i.val

/-- Equation (49) of arXiv:1509.09271v2: on good inputs the recurrence
coefficients are uniquely determined by the power sums `z_0, …, z_{2k-1}`, so the
characteristic polynomial `χ` of equation (50) is determined by `z` alone. -/
theorem recCoeff_unique (x y : Fin k → F) (hx : Function.Injective x)
    (hy : ∀ i, y i ≠ 0) {a : Fin k → F}
    (ha : (hankel x y).mulVec a = fun i => powerSum x y (i.val + k)) :
    a = fun j => recCoeff x j.val := by
  refine hankel_mulVec_injective x y hx hy ?_
  rw [ha, hankel_mulVec_recCoeff]

end Qatlib.Papers.PolynomialInt15.MainResults
