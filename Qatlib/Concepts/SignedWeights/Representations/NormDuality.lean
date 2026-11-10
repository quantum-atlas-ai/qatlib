/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.NormDuality

noncomputable section

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
