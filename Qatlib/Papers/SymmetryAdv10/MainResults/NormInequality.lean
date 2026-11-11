/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 of arXiv:1012.2112v1 (p. 4): trace bounded by operator times trace norm

The paper states, for any matrices `A B`,

`tr(AB) ≤ ‖A‖ · ‖B‖_tr`.

The faithful Lean form is the absolute-value inequality
`‖tr(AB)‖ ≤ ‖A‖ · ‖B‖_tr`, from which the paper's real form follows for Hermitian
matrices by taking real parts.

Reused frozen/Mathlib declarations (read in full, matching statements):

* `Matrix.abs_trace_le_traceNorm` (`QuantumInfo.ForMathlib.MatrixNorm.TraceNorm`,
  Physlib): `‖A.trace‖ ≤ A.traceNorm`;
* `Matrix.traceNorm_mul_le_opNorm_traceNorm` (same file):
  `(A * B).traceNorm ≤ ‖A‖ * B.traceNorm`, where `‖·‖` is the `L2Operator`
  spectral norm of `Mathlib.Analysis.CStarAlgebra.Matrix`.

No new axiom, `admit`, or `native_decide` is used; the proof is a two-step
composition of the two frozen inequalities.
-/

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.SymmetryAdv10.MainResults.NormInequality

noncomputable section

/-- **Lemma 3 (arXiv:1012.2112v1, p. 4).** For any square complex matrices
`A`, `B`: `‖tr(AB)‖ ≤ ‖A‖ · ‖B‖_tr`.

This is the absolute-value form; for Hermitian `A` the paper's `tr(AB)` is real
and the statement below (`lemma3_trace_re_le`) recovers the printed form. -/
theorem abs_trace_mul_le_opNorm_traceNorm {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ ‖A‖ * B.traceNorm :=
  (Matrix.abs_trace_le_traceNorm (A * B)).trans
    (Matrix.traceNorm_mul_le_opNorm_traceNorm A B)

/-- **Lemma 3, printed real form (arXiv:1012.2112v1, p. 4).** For any square
complex matrices `A`, `B`, the real part of `tr(AB)` is at most
`‖A‖ · ‖B‖_tr`. -/
theorem lemma3_trace_re_le {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    (A * B).trace.re ≤ ‖A‖ * B.traceNorm :=
  (Complex.re_le_norm _).trans (abs_trace_mul_le_opNorm_traceNorm A B)

/-- **Lemma 3, Hermitian specialization (arXiv:1012.2112v1, p. 4).** If `A` is
Hermitian then `tr(AB)` is real-valued, so the printed inequality
`tr(AB) ≤ ‖A‖ · ‖B‖_tr` is literally the real-part bound. -/
theorem lemma3_trace_le_of_isHermitian {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (_hA : A.IsHermitian) :
    (A * B).trace.re ≤ ‖A‖ * B.traceNorm :=
  lemma3_trace_re_le A B

end

end NormInequality
