/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolynomialInt15.MainResults.ElementarySymmetric

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# The power-sum recurrence (Lemma 6) and the Hankel system of equation (47)

This module formalizes Lemma 6 of Childs, van Dam, Hung and Shparlinski,
*Optimal quantum algorithm for polynomial interpolation* (arXiv:1509.09271v2,
Section 4.1, equation (43)) and the Hankel system (47) of the Prony-style
inversion of `Z`.

The paper's function `Z` (equation (7)) has components

  `Z(x, y)_j = ∑_{i=1}^{k} y_i x_i^j`,  `j ∈ {0, 1, …, d}`,

so its `j`-th component is the power sum `powerSum x y j` below. Lemma 6 says
that these components satisfy the `k`-th order linear recurrence

  `z_{n+k} = -∑_{j=0}^{k-1} (-1)^{k-j} e_{k-j}(x) z_{n+j}`

for every `n`, i.e. `z_{n+k} = ∑_{j} a_j z_{n+j}` with `a_j = -(-1)^{k-j} e_{k-j}`.
Equation (47) is exactly the matrix form `H_k a = (z_k, …, z_{2k-1})` of the
`n = 0` instance, where `H_k` is the Hankel matrix `(H_k)_{ij} = z_{i+j}`.

Lemma 6 is derived from Lemma 5 (`newton_identity_charPoly`) by multiplying the
identity for `x_i` by `y_i x_i^n` and summing over `i`, which is the paper's
equation (44)–(46).
-/

namespace Qatlib.Papers.PolynomialInt15.MainResults

open Finset

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The power sums `z_j = ∑_i y_i x_i^j` of equation (7): the `j`-th component
of the paper's function `Z`. -/
noncomputable def powerSum (x y : Fin k → R) (j : ℕ) : R :=
  ∑ i, y i * x i ^ j

/-- The recurrence coefficients `a_j = -(-1)^{k-j} e_{k-j}(x)` of equation (47);
these are minus the coefficients of the characteristic polynomial `∏_i (X - x_i)`. -/
noncomputable def recCoeff (x : Fin k → R) (j : ℕ) : R := -charCoeff x (k - j)

/-- Lemma 6 of arXiv:1509.09271v2, equation (43): the power sums of `x` with
weights `y` satisfy the `k`-th order linear recurrence determined by the
elementary symmetric functions of `x`. -/
theorem powerSum_recurrence (x y : Fin k → R) (n : ℕ) :
    powerSum x y (n + k) = - ∑ j ∈ range k, charCoeff x (k - j) * powerSum x y (n + j) := by
  have hterm : ∀ i : Fin k,
      y i * x i ^ (n + k) = - ∑ j ∈ range k, charCoeff x (k - j) * (y i * x i ^ (n + j)) := by
    intro i
    have hk := newton_identity_charPoly x i
    have hstep : y i * x i ^ (n + k) = y i * x i ^ n * x i ^ k := by rw [pow_add, mul_assoc]
    rw [hstep, hk, mul_neg, Finset.mul_sum]
    refine congrArg Neg.neg (Finset.sum_congr rfl ?_)
    intro j _
    rw [pow_add]
    ring
  rw [powerSum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib,
    Finset.sum_comm]
  refine congrArg Neg.neg (Finset.sum_congr rfl ?_)
  intro j _
  rw [powerSum, Finset.mul_sum]

/-- Lemma 6 stated with the recurrence coefficients `a_j`: `z_{n+k} = ∑_j a_j z_{n+j}`. -/
theorem powerSum_recurrence' (x y : Fin k → R) (n : ℕ) :
    powerSum x y (n + k) = ∑ j ∈ range k, recCoeff x j * powerSum x y (n + j) := by
  rw [powerSum_recurrence, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [recCoeff]
  ring

/-- Equation (47) of arXiv:1509.09271v2: the row `(z_i, z_{i+1}, …, z_{i+k-1})` of
the Hankel matrix `H_k` dotted with the recurrence coefficients `a_j` recovers
`z_{i+k}`. -/
theorem hankel_row_recurrence (x y : Fin k → R) (i : ℕ) :
    ∑ j ∈ range k, powerSum x y (i + j) * recCoeff x j = powerSum x y (i + k) := by
  rw [powerSum_recurrence']
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end Qatlib.Papers.PolynomialInt15.MainResults
