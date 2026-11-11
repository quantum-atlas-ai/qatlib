/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 4 — trace-norm duality

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 4, §2, printed page 8:

For `n`-by-`n` matrices `A`, `B`, `|⟨A,B⟩| ≤ ‖A‖ · ‖B‖_tr`, where
`⟨A,B⟩ = tr(A†B)` is the Hilbert–Schmidt inner product, `‖A‖` is the
spectral (L2 operator) norm and `‖B‖_tr` is the trace norm.

The proof is the paper's two-step route: the absolute trace is bounded by the
trace norm (`Matrix.abs_trace_le_traceNorm`), and the trace norm is submultiplicative
against the operator norm (`Matrix.traceNorm_mul_le_opNorm_traceNorm`), with
`‖A†‖ = ‖A‖` (`Matrix.l2_opNorm_conjTranspose`).
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.NormDuality

noncomputable section

/-- **Theorem 4 (trace-norm duality).**
For square complex matrices `A B : Matrix (Fin n) (Fin n) ℂ`,
`|tr(A† B)| ≤ ‖A‖ · ‖B‖_tr`.

The Hilbert–Schmidt inner product of the paper is `⟨A,B⟩ = tr(A†B)`, so this is
exactly `|⟨A,B⟩| ≤ ‖A‖ · ‖B‖_tr` (quant-ph/0611054v2 Theorem 4, p. 8). -/
theorem theorem4_trace_duality (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ ‖A‖ * B.traceNorm := by
  calc
    ‖Matrix.trace (Aᴴ * B)‖ ≤ (Aᴴ * B).traceNorm :=
      Matrix.abs_trace_le_traceNorm (Aᴴ * B)
    _ ≤ ‖Aᴴ‖ * B.traceNorm :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm Aᴴ B
    _ = ‖A‖ * B.traceNorm := by rw [Matrix.l2_opNorm_conjTranspose]

end

end Qatlib.Papers.NegWeights06.MainResults.NormDuality
