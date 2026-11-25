/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseNetwork13.MainResults.Spectral.EigenphaseGap

@[expose] public section

/-!
# The closing estimate of Corollary 1.11

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1, Corollary 1.11
(p. 5).

The proof of Corollary 1.11 bounds the phase gap `Δ(-U)` of a two-reflection unitary by
twice the smallest singular value of its discriminant: with `σ = σ_min(D)` and
`θ = arccos σ` the source uses `π - 2θ ≥ 2σ` when `σ ∈ [0, 1]`.  Written with the
absolute value used by the source's `|π - 2 arccos σ_min(D)|` this is
`2σ ≤ |π - 2 arccos σ|`.

The numerical core `σ ≤ π/2 - arccos σ` is the already published eigenphase-gap estimate
`Qatlib.Papers.SparseNetwork13.MainResults.Spectral.sin_arccos_gap`; the remaining step
only uses `arccos σ ≤ π/2` for `σ ≥ 0` to remove the absolute value.  Connecting this
scalar estimate to `Qatlib.Papers.ApproxSpan15.MainResults.SpanProgram.phaseGap` (whose
value is the `2 sin(θ/2)` form of the phase distance) still needs the explicit angular
conversion recorded as a model gap in the paper-layer boundary.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxSpan15.MainResults

/-- **arXiv:1507.00432v1, proof of Corollary 1.11 (p. 5).**  For `σ ∈ [0, 1]` the
phase distance `|π - 2 arccos σ|` is at least `2σ`, which is the estimate used to deduce
`Δ(-U) ≥ 2 σ_min(D)`. -/
theorem abs_pi_sub_two_arccos_ge (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    2 * s ≤ |Real.pi - 2 * Real.arccos s| := by
  have hgap : s ≤ Real.pi / 2 - Real.arccos s :=
    Qatlib.Papers.SparseNetwork13.MainResults.Spectral.sin_arccos_gap s h0 h1
  have hle : Real.arccos s ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr h0
  have hnonneg : 0 ≤ Real.pi - 2 * Real.arccos s := by linarith
  rw [abs_of_nonneg hnonneg]
  linarith

end Qatlib.Papers.ApproxSpan15.MainResults
