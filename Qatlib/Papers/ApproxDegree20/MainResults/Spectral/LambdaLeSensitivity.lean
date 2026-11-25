/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Spectral.SensitivityAdjacency

@[expose] public section

/-!
# Spectral sensitivity is bounded by the sensitivity

Source: arXiv:2010.12629v1, §3 (page 6), the first step of Huang's argument: for every total
Boolean function `f` the spectral sensitivity `λ(f)` is at most the sensitivity `s(f)`.

`λ(f)` is the `L2` operator norm of the sensitivity graph
`Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.sensAdjacency f`, whose absolute row and
column sums at an input `x` equal the vertex sensitivity `s_x(f)`. The Schur test then bounds
the operator norm by the maximum vertex sensitivity.

Boundary: `f` is a total Boolean function on an arbitrary finite coordinate type `I`; the
paper's `{0,1}^n` is `I = Fin n`. Partially defined functions are not covered.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds (sensAdjacency spectralSensitivity)
open Qatlib.Papers.ApproxDegree20.MainResults.Definitions
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ApproxDegree20.MainResults.Spectral

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The spectral sensitivity `λ(f)` of a total Boolean function is at most its sensitivity
`s(f)`, the maximum number of sensitive coordinates of an input. -/
theorem spectralSensitivity_le_sensitivity (f : (I → Bool) → Bool) :
    spectralSensitivity f ≤ (sensitivity f : ℝ) := by
  have hC : (0 : ℝ) ≤ (sensitivity f : ℝ) := by positivity
  have hrow : ∀ x : I → Bool, (∑ y, ‖sensAdjacency f x y‖) ≤ (sensitivity f : ℝ) :=
    rowSum_le_sensitivity f
  have hcol : ∀ y : I → Bool, (∑ x, ‖sensAdjacency f x y‖) ≤ (sensitivity f : ℝ) := by
    intro y
    rw [colSum_sensAdjacency, ← rowSum_sensAdjacency]
    exact rowSum_le_sensitivity f y
  simpa only [spectralSensitivity] using
    norm_le_of_rowSum_colSum_le (sensAdjacency f) hC hrow hcol

end Qatlib.Papers.ApproxDegree20.MainResults.Spectral
