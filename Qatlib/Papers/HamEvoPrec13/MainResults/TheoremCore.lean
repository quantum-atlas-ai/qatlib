/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Qatlib.Papers.HamEvoPrec13.MainResults.SparseDecomposition

/-!
# Theorem 1: the exact exponential of a commuting self-inverse decomposition

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, proof of Theorem 1, step 3, and Eq. (5).

Theorem 1 approximates the evolution under a sparse Hamiltonian `H` by a Lie--Trotter
product over `1`-sparse pieces, then invokes Lemma 1 to write each piece as an equally
weighted sum of commuting self-inverse Hamiltonians `U_l`.  The key structural fact in
step 3 is that because the `U_l` commute, the exponential of their weighted sum is
*exactly* the product of the individual exponentials, with no additional error:

    exp(∑_l w_l • U_l) = ∏_l exp(w_l • U_l).

`exp_sum_of_pairwise_commute` records this exact factorisation in Mathlib's form,
using `Finset.noncommProd` because `Matrix` is not commutative.

This file also formalises the projection algebra behind Eq. (5) (`proj_idempotent`,
`projQ_idempotent`, `proj_add`, `proj_orthogonal`): for a self-inverse `U`, the
operators `P = (1+U)/2` and `Q = (1-U)/2` are complementary orthogonal idempotents,
which is the algebraic content of writing `exp(-i s U) = cos s · 1 - i sin s · U`.

The remaining parts of Theorem 1's proof (the Trotter error estimate, the oracle and
gate count arithmetic, and the asymptotic composition into Eq. (1)) are not covered by
this file.
-/

set_option autoImplicit false
open scoped Function

noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.MainResults

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of a finite sum of pairwise commuting matrices is the
(noncommutative) product of the exponentials. This is the exact factorisation used in
step 3 of the proof of Theorem 1: the self-inverse Hamiltonians `U_l` commute, so
exponentiating their weighted sum introduces no error. -/
theorem exp_sum_of_pairwise_commute {ι : Type*} (s : Finset ι)
    (f : ι → Matrix n n ℂ) (h : (s : Set ι).Pairwise (Commute on f)) :
    NormedSpace.exp (∑ i ∈ s, f i)
      = s.noncommProd (fun i => NormedSpace.exp (f i))
          (fun _ hi _ hj _ => (h.of_refl hi hj).exp) :=
  Matrix.exp_sum_of_commute s f h

/-- The projection `P = (1+U)/2` of a self-inverse matrix is idempotent. This is one
half of the algebraic content of Eq. (5): the spectrum of `U` is contained in `{±1}`. -/
theorem proj_idempotent (U : Matrix n n ℂ) (hU : U * U = 1) :
    ((1 / 2 : ℂ) • (1 + U)) * ((1 / 2 : ℂ) • (1 + U)) = (1 / 2 : ℂ) • (1 + U) := by
  have hexp : (1 + U) * (1 + U) = (1 + U) + (1 + U) := by
    noncomm_ring [hU]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, smul_add, ← add_smul]
  have hc : (1 / 2 * (1 / 2) : ℂ) + 1 / 2 * (1 / 2) = 1 / 2 := by norm_num
  rw [hc]

/-- The complementary projection `Q = (1-U)/2` of a self-inverse matrix is idempotent. -/
theorem projQ_idempotent (U : Matrix n n ℂ) (hU : U * U = 1) :
    ((1 / 2 : ℂ) • (1 - U)) * ((1 / 2 : ℂ) • (1 - U)) = (1 / 2 : ℂ) • (1 - U) := by
  have hexp : (1 - U) * (1 - U) = (1 - U) + (1 - U) := by
    noncomm_ring [hU]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, smul_add, ← add_smul]
  have hc : (1 / 2 * (1 / 2) : ℂ) + 1 / 2 * (1 / 2) = 1 / 2 := by norm_num
  rw [hc]

omit [Fintype n] in
/-- The two projections of a self-inverse matrix sum to the identity. -/
theorem proj_add (U : Matrix n n ℂ) :
    (1 / 2 : ℂ) • (1 + U) + (1 / 2 : ℂ) • (1 - U) = 1 := by
  rw [← smul_add]
  have hexp : (1 + U) + (1 - U) = (1 : Matrix n n ℂ) + 1 := by abel
  rw [hexp, smul_add, ← add_smul]
  have hc : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  rw [hc, one_smul]

/-- The two projections of a self-inverse matrix are orthogonal. -/
theorem proj_orthogonal (U : Matrix n n ℂ) (hU : U * U = 1) :
    ((1 / 2 : ℂ) • (1 + U)) * ((1 / 2 : ℂ) • (1 - U)) = 0 := by
  have hexp : (1 + U) * (1 - U) = 0 := by
    noncomm_ring [hU]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, smul_zero]

/-- With `γ = ε/(t√d)` the spectral-norm conversion `‖H - H̃‖ ≤ √d ‖H - H̃‖_max` gives
the operator error budget `√d·γ = ε/t`, the value used in the proof of Theorem 1 to
make the discretisation error `O(ε)`. -/
theorem gamma_sqrt_d (γ ε t : ℝ) (d : ℕ) (ht : 0 < t) (hd : 0 < d)
    (hγ : γ = ε / (t * Real.sqrt d)) :
    Real.sqrt d * γ = ε / t := by
  rw [hγ]
  have hd0 : (Real.sqrt d) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd))
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp

end Qatlib.Papers.HamEvoPrec13.MainResults
