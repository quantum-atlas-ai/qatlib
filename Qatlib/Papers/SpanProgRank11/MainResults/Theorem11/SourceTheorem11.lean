/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — Theorem 11 (claim c002)

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1, Sec. 4.1, Theorem 11, p. 8.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults.Theorem11

open Qatlib.Papers.SpanProgRank11.MainResults
open scoped BigOperators ENNReal

/-- A high-level span program together with a matrix-loading subroutine that
realises it as an actual span program of witness size at most
`L · wsize(P)`.  `L` is exactly the paper's "complexity of loading matrix `A`
into the span program" (Sec. 4.1, p. 8; concretely one of Subroutines
13/15/16). -/
structure LoadedSpanProgram where
  /-- The witness size `wsize(P)` of the high-level program. -/
  wsizeP : ℝ
  /-- The witness size of the loaded actual span program. -/
  wsizeLow : ℝ
  /-- The loading complexity `L`. -/
  loadingFactor : ℝ
  /-- `wsize(P)` is nonnegative. -/
  wsizeP_nonneg : 0 ≤ wsizeP
  /-- The loaded witness size is nonnegative. -/
  wsizeLow_nonneg : 0 ≤ wsizeLow
  /-- The loading complexity is nonnegative. -/
  loadingFactor_nonneg : 0 ≤ loadingFactor
  /-- The loading subroutine produces an actual span program with witness size
  at most `L · wsize(P)` (the conclusion of Subroutines 13/15/16). -/
  loaded : wsizeLow ≤ loadingFactor * wsizeP

/-- The query count of the algorithm obtained by (i) loading the matrix into
the span program and (ii) applying Reichardt's span-program-to-query-algorithm
theorem (paper Theorem 2, p. 4): `C_T` times the witness size of the loaded
program. -/
def loadedQueryCount (C_T : ℝ) (lowLevelWitnessSize : ℝ) : ℝ :=
  C_T * lowLevelWitnessSize

/-- **Fixed arXiv:1103.0842v1, Theorem 11 (Sec. 4.1, p. 8).**
Any high-level span program `𝒫` can be solved by a quantum query algorithm of
complexity `O(wsize(𝒫) · L)`, where `L` is the complexity of loading the matrix
`A` into the span program.

Lean content is the cost-composition core: Theorem 2 (p. 4) gives a two-sided
bounded-error quantum algorithm using `C_T · wsize` queries (its constant `C_T`
is the source constant of Reichardt [21,20]); the loading subroutine of Sec. 5
produces an actual span program of witness size `≤ L · wsize(𝒫)`.  Composing,
`C_T · wsizeLow ≤ C_T · wsize(𝒫) · L`, i.e. `O(wsize(𝒫) · L)`.

The structural span-program-to-graph translation of Reichardt is the already
available `Qatlib.Concepts.QueryComplexity.Reflections` layer; this
file records only the cost arithmetic. -/
theorem source_theorem11 (C_T : ℝ) (hC_T : 0 < C_T) (P : LoadedSpanProgram) :
    ∃ C : ℝ, 0 < C ∧
      loadedQueryCount C_T P.wsizeLow ≤ C * P.wsizeP * P.loadingFactor := by
  refine ⟨C_T, hC_T, ?_⟩
  unfold loadedQueryCount
  calc
    C_T * P.wsizeLow ≤ C_T * (P.loadingFactor * P.wsizeP) :=
      mul_le_mul_of_nonneg_left P.loaded hC_T.le
    _ = C_T * P.wsizeP * P.loadingFactor := by ring

end Qatlib.Papers.SpanProgRank11.MainResults.Theorem11
