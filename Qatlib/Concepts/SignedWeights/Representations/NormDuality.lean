/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Operator and Trace Norm Pairing

This module proves the operator-norm and trace-norm pairing estimate used in the adversary
analysis of [HoyerLeeSpalek2007]. For finite complex square matrices, the absolute trace of
`A`'s adjoint times `B` is at most the operator norm of `A` times `B.traceNorm`. The proof
combines the trace bound, the mixed product bound, and invariance of the operator norm under the
adjoint.

## Main statements

- `theorem4_trace_duality` proves the trace pairing inequality.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Theorem 4.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.NormDuality

noncomputable section

/-- The absolute trace of the adjoint of `A` multiplied by `B` is bounded by the operator norm
of `A` times the trace norm of `B`, as in Theorem 4 of [HoyerLeeSpalek2007]. -/
theorem theorem4_trace_duality (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ ‖A‖ * B.traceNorm := by
  calc
    ‖Matrix.trace (Aᴴ * B)‖ ≤ (Aᴴ * B).traceNorm :=
      Matrix.abs_trace_le_traceNorm (Aᴴ * B)
    _ ≤ ‖Aᴴ‖ * B.traceNorm :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm Aᴴ B
    _ = ‖A‖ * B.traceNorm := by rw [Matrix.l2_opNorm_conjTranspose]

end

end Qatlib.Concepts.SignedWeights.Representations.NormDuality
