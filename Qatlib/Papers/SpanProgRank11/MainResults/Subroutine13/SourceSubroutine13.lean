/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — Subroutine 13 (claim c005)

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1, Subroutine 13 in Sec. 5.2, p. 13 (proof p. 13).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults.Subroutine13

open Qatlib.Papers.SpanProgRank11.MainResults
open scoped BigOperators ENNReal

/-- The loading complexity of the dense matrix-loading subroutine:
`O(√(nm))` (Subroutine 13, p. 13). -/
def denseLoadingFactor (n m : ℕ) : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ))

/-- **Fixed arXiv:1103.0842v1, Subroutine 13 (Sec. 5.2, p. 13), cost identity.**
Composing `m` copies of the vector-loading subroutine (Subroutine 12) multiplies
the positive witness size by `n` and the negative witness size by `m`; its
geometric mean — the witness size — is multiplied by `√(nm)`.

Source proof (p. 13): "In the positive case, the contribution of `Lⱼ` is
`O(n wⱼ²)` … the positive witness size of the composed program is `O(n ‖w‖²)`.
In the negative case … the negative witness size is `O(m ‖w'‖²)`.  The total
witness size can be obtained as the geometrical mean."  Here `w₁`, `w₀` are the
source `wsize₁`, `wsize₀`; no other constant is introduced. -/
theorem source_subroutine13_witness_identity (n m : ℕ) (w1 w0 : ℝ)
    (h1 : 0 ≤ w1) (h0 : 0 ≤ w0) :
    geometricWitnessSize ((n : ℝ) * w1) ((m : ℝ) * w0)
      = denseLoadingFactor n m * geometricWitnessSize w1 w0 := by
  calc
    geometricWitnessSize ((n : ℝ) * w1) ((m : ℝ) * w0)
        = Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) * geometricWitnessSize w1 w0 :=
          geometricWitnessSize_scale (n : ℝ) (m : ℝ) w1 w0
            (by positivity) (by positivity) h1 h0
    _ = denseLoadingFactor n m * geometricWitnessSize w1 w0 := by
          rw [denseLoadingFactor, Real.sqrt_mul (by positivity)]

/-- **Fixed arXiv:1103.0842v1, Subroutine 13 (Sec. 5.2, p. 13).**
Any high-level span program `𝒫` for `n × m` matrices can be implemented as an
actual span program with witness size at most `O(√(nm) · wsize(𝒫))`, i.e. the
complexity of the subroutine is `O(√(nm))`.

This is the "at most" form of `source_subroutine13_witness_identity`: the
composed witness size equals `√(nm)` times the source witness size, with the
witness-size bounds `w₁`, `w₀` as the positive/negative component bounds. -/
theorem source_subroutine13 (n m : ℕ) (w1 w0 : ℝ) (h1 : 0 ≤ w1) (h0 : 0 ≤ w0) :
    geometricWitnessSize ((n : ℝ) * w1) ((m : ℝ) * w0)
      ≤ denseLoadingFactor n m * geometricWitnessSize w1 w0 :=
  le_of_eq (source_subroutine13_witness_identity n m w1 w0 h1 h0)

/-- The dense loading factor is `√n · √m`, the explicit form used in the
`O(√(nm))` complexity statement. -/
theorem denseLoadingFactor_eq (n m : ℕ) :
    denseLoadingFactor n m = Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
  rw [denseLoadingFactor, Real.sqrt_mul (by positivity)]

end Qatlib.Papers.SpanProgRank11.MainResults.Subroutine13
