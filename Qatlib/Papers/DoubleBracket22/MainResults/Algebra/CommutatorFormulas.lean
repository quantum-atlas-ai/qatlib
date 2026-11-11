/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket22.MainResults.Model.DoubleBracketModel

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket22 — Lemma 6 (commMat formulas)

Source: arXiv:2206.11772v4, Lemma 6, Eqs. (76)–(78), printed p. 24.

The paper proves three linear-algebra identities used throughout the appendix:
the difference of two commutators is a sum of commutators of differences
(Eq. (76)); the trace is cyclic on `A[B,C]` (Eq. (77)); and consequently
`tr A[B,A] = 0` (Eq. (78)). All three are proved here for arbitrary complex
square matrices.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators

namespace Qatlib.Papers.DoubleBracket22.MainResults.Algebra

open Qatlib.Papers.DoubleBracket22.MainResults.Model

/-- Lemma 6, Eq. (76), p. 24. For any `A,B,C,X ∈ L(ℂ×D)`,
`[A,B] − [C,X] = [A−C, B] + [C, B−X]`.

Proved exactly as the paper: expand both sides and use bilinearity of the
bracket (`noncomm_ring` for the non-commutative matrix algebra). -/
theorem lemma6_commutatorDiff {D : ℕ} (A B C X : Mat D) :
    commMat A B - commMat C X = commMat (A - C) B + commMat C (B - X) := by
  unfold commMat
  noncomm_ring

/-- Lemma 6, Eq. (77), p. 24. Trace cyclicity: `tr(A[B,C]) = tr(B[C,A])`.

Proof as in the paper (Eqs. (80)–(81)): expand `[B,C]` and `[C,A]` and use
`trace_mul_comm` to cycle each monomial to a common form. -/
theorem lemma6_traceCyclicity {D : ℕ} (A B C : Mat D) :
    (A * commMat B C).trace = (B * commMat C A).trace := by
  unfold commMat
  rw [mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub]
  -- LHS = tr(A B C) − tr(A C B), RHS = tr(B C A) − tr(B A C)
  have h1 : (A * (B * C)).trace = (B * (C * A)).trace := by
    rw [Matrix.trace_mul_comm A (B * C), Matrix.mul_assoc]
  have h2 : (A * (C * B)).trace = (C * (B * A)).trace := by
    rw [Matrix.trace_mul_comm A (C * B), Matrix.mul_assoc]
  have h3 : (C * (B * A)).trace = (B * (A * C)).trace := by
    rw [Matrix.trace_mul_comm C (B * A), Matrix.mul_assoc]
  rw [h1, h2, h3]

/-- Lemma 6, Eq. (78), p. 24. `tr(A[B,A]) = 0`.

Proof: apply Eq. (77) with `C = A`; the right side is `tr(B[A,A]) = tr(B·0) = 0`. -/
theorem lemma6_traceSelfCommutator {D : ℕ} (A B : Mat D) :
    (A * commMat B A).trace = 0 := by
  have h := lemma6_traceCyclicity A B A
  simpa [commMat] using h

end Qatlib.Papers.DoubleBracket22.MainResults.Algebra
