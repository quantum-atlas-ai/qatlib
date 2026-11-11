/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket22.MainResults.Model.DoubleBracketModel

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket22 — Lemma 8 (diagonal–off-diagonal orthogonality)

Source: arXiv:2206.11772v4, Lemma 8, Eq. (89), printed p. 25.

For any `A,B ∈ L(ℂ×D)` the Hilbert–Schmidt product of the off-diagonal
restriction `σ(A)` with the diagonal restriction `Δ(B)` vanishes:
`tr(σ(A) Δ(B)) = 0`.

Proof follows the paper (Eqs. (90)–(92)): in a basis, `σ(A) Δ(B)` remains
off-diagonal because right multiplication by a diagonal operator only rescales
columns and the diagonal entries of `σ(A)` are zero; the trace picks out the
diagonal, hence vanishes.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators

namespace Qatlib.Papers.DoubleBracket22.MainResults.Algebra

open Qatlib.Papers.DoubleBracket22.MainResults.Model

/-- Entry formula used for the trace of a product with a diagonal matrix:
`tr(A * diagonal v) = Σᵢ Aᵢᵢ vᵢ`. -/
theorem trace_mul_diagonal {D : ℕ} (A : Mat D) (v : Fin D → ℂ) :
    (A * Matrix.diagonal v).trace = ∑ i, A i i * v i := by
  change (∑ i, (A * Matrix.diagonal v) i i) = ∑ i, A i i * v i
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.diagonal_apply_eq]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ hji, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Lemma 8, Eq. (89), p. 25. `tr(σ(A) Δ(B)) = 0`.

Proved by the paper's direct computation: `σ(A) Δ(B)` has zero diagonal, so
its trace vanishes.  Concretely `tr((A − ΔA) ΔB) = tr(A ΔB) − tr(ΔA ΔB)` and
both terms equal `Σᵢ Aᵢᵢ Bᵢᵢ`. -/
theorem lemma8_diagonalOffDiagonalOrthogonality {D : ℕ} (A B : Mat D) :
    (offDiag A * diagPart B).trace = 0 := by
  unfold offDiag diagPart
  rw [Matrix.sub_mul, Matrix.trace_sub]
  have hA : (A * Matrix.diagonal (fun i => B i i)).trace = ∑ i, A i i * B i i :=
    trace_mul_diagonal A (fun i => B i i)
  have hD : (Matrix.diagonal (fun i => A i i) * Matrix.diagonal (fun i => B i i)).trace
      = ∑ i, A i i * B i i := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [Matrix.trace, Matrix.diagonal]
  rw [hA, hD, sub_self]

end Qatlib.Papers.DoubleBracket22.MainResults.Algebra
