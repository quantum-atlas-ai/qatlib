/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option backward.isDefEq.respectTransparency false

/-! Trace-power identities for
"Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes" (arXiv:2408.16934v3, 2025).

Lemma 3.2 of the paper: for a Hermitian positive semidefinite matrix
`M = D†D`, the trace of `M^d` is the sum over computational basis
vectors of the squared norms `‖D^(d)|x⟩‖²`, where `D^(d)` is
`(D†D)^{d/2}` for even `d` and `(DD†)^{(d-1)/2} D` for odd `d`.

- `trace_star_mul_self` is the Frobenius identity
  `tr(A†A) = ∑_x ‖A e_x‖²` (as `∑_x ∑_i ‖A i x‖²`).
- `shift_pow_eq` is the commutation identity
  `(DD†)^k D = D (D†D)^k`.
- `trace_pow_even` / `trace_pow_odd` are the two parities of Lemma 3.2.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.BettiNumber25.MainResults.TracePower

open scoped Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Frobenius trace identity: `tr(Aᴴ A)` is the sum over columns of the
squared norms `‖A e_x‖²` (the inner sum `∑ i ‖A i x‖²` is `‖A e_x‖²`;
`Complex.normSq z` is `‖z‖²`). -/
theorem trace_star_mul_self (A : Matrix m n ℂ) :
    (Aᴴ * A).trace = ∑ x : n, ∑ i : m, ((Complex.normSq (A i x) : ℝ) : ℂ) := by
  classical
  have h1 : ∀ i : n, (Aᴴ * A) i i = ∑ j : m, ((Complex.normSq (A j i) : ℝ) : ℂ) := by
    intro i
    have h2 : ∀ j : m, star (A j i) * A j i = ((Complex.normSq (A j i) : ℝ) : ℂ) :=
      fun j => (Complex.normSq_eq_conj_mul_self).symm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun j _ => h2 j
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun i _ => h1 i

/-- The shift commutation identity: powers of `DD†` push through `D`,
`(DD†)^k D = D (D†D)^k`. -/
theorem shift_pow_eq (D : Matrix m n ℂ) (k : ℕ) :
    (D * Dᴴ) ^ k * D = D * (Dᴴ * D) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (D * Dᴴ) ^ (k + 1) * D = ((D * Dᴴ) ^ k * (D * Dᴴ)) * D := by rw [pow_succ]
        _ = (D * Dᴴ) ^ k * ((D * Dᴴ) * D) := by rw [Matrix.mul_assoc]
        _ = (D * Dᴴ) ^ k * (D * (Dᴴ * D)) := by rw [Matrix.mul_assoc D Dᴴ D]
        _ = ((D * Dᴴ) ^ k * D) * (Dᴴ * D) := by rw [← Matrix.mul_assoc]
        _ = (D * (Dᴴ * D) ^ k) * (Dᴴ * D) := by rw [ih]
        _ = D * ((Dᴴ * D) ^ k * (Dᴴ * D)) := by rw [Matrix.mul_assoc]
        _ = D * (Dᴴ * D) ^ (k + 1) := by rw [pow_succ]

omit [DecidableEq m] in
/-- **Lemma 3.2, even case**: for `M = D†D` and `d = 2k`,
`tr(M^d) = ∑_x ‖(D†D)^k e_x‖²`. -/
theorem trace_pow_even (D : Matrix m n ℂ) (k : ℕ) :
    ((Dᴴ * D) ^ (2 * k)).trace = ∑ x : n, ∑ i : n,
      ((Complex.normSq (((Dᴴ * D) ^ k) i x) : ℝ) : ℂ) := by
  have hH : (Dᴴ * D).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self D
  have hk : ((Dᴴ * D) ^ k)ᴴ = (Dᴴ * D) ^ k := hH.pow k
  have hprod : ((Dᴴ * D) ^ k)ᴴ * ((Dᴴ * D) ^ k) = (Dᴴ * D) ^ (2 * k) := by
    rw [hk, two_mul, pow_add]
  rw [← hprod]
  exact trace_star_mul_self _

/-- **Lemma 3.2, odd case**: for `M = D†D` and `d = 2k+1`,
`tr(M^d) = ∑_x ‖(DD†)^k D e_x‖²`. -/
theorem trace_pow_odd (D : Matrix m n ℂ) (k : ℕ) :
    ((Dᴴ * D) ^ (2 * k + 1)).trace = ∑ x : n, ∑ i : m,
      ((Complex.normSq (((D * Dᴴ) ^ k * D) i x) : ℝ) : ℂ) := by
  have hH' : (D * Dᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  have hk' : ((D * Dᴴ) ^ k)ᴴ = (D * Dᴴ) ^ k := hH'.pow k
  have hsq : (((D * Dᴴ) ^ k * D)ᴴ) * ((D * Dᴴ) ^ k * D) = (Dᴴ * D) ^ (2 * k + 1) := by
    calc (((D * Dᴴ) ^ k * D)ᴴ) * ((D * Dᴴ) ^ k * D)
        = (Dᴴ * (D * Dᴴ) ^ k) * ((D * Dᴴ) ^ k * D) := by
          rw [Matrix.conjTranspose_mul, hk']
      _ = Dᴴ * (((D * Dᴴ) ^ k * (D * Dᴴ) ^ k) * D) := by
          rw [← Matrix.mul_assoc, Matrix.mul_assoc Dᴴ ((D * Dᴴ) ^ k) ((D * Dᴴ) ^ k),
            Matrix.mul_assoc Dᴴ ((D * Dᴴ) ^ k * (D * Dᴴ) ^ k) D]
      _ = Dᴴ * ((D * Dᴴ) ^ (k + k) * D) := by rw [pow_add]
      _ = Dᴴ * (D * (Dᴴ * D) ^ (k + k)) := by rw [shift_pow_eq]
      _ = (Dᴴ * D) * (Dᴴ * D) ^ (k + k) := by
          rw [Matrix.mul_assoc Dᴴ D ((Dᴴ * D) ^ (k + k))]
      _ = (Dᴴ * D) ^ (k + k + 1) := by rw [← pow_succ']
      _ = (Dᴴ * D) ^ (2 * k + 1) := by rw [two_mul]
  rw [← hsq]
  exact trace_star_mul_self _

end Qatlib.Papers.BettiNumber25.MainResults.TracePower
