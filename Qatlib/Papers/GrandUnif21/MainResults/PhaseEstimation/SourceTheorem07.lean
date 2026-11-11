/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 7 — error bound when `n < m`

Source: arXiv:2105.02859v3, Theorem 7 (Sec. V A 2, metadata line 835).

If the target phase `φ ∈ [0,1)` needs more than `n` bits and the sign function
is implemented exactly through QSVT, then at the end of the procedure
`|θ − φ| ≤ 2^{-n-1}`: the output is the nearest `n`-bit number, i.e. nearest
rounding to `n` binary places, whose error is at most half a unit in the last
place.  The rounding model is `roundDyadic n φ` of `SourceModel`; the error
bound is `abs_roundDyadic_sub_le`.

Boundary: the arithmetic rounding error only.  The paper's proof (Appendix B,
Eqs. (B9)--(B10)) argues that the QSVT sign evaluation realizes exactly this
rounding at every iteration; that realization is not modelled here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

/-- GrandUnif21 Theorem 7 (arXiv:2105.02859v3, metadata line 835): for a phase
`φ ∈ [0,1)` and `n` iterations, the final register value `θ = roundDyadic n φ`
satisfies `|θ − φ| ≤ 2^{-n-1}`. -/
theorem source_theorem7 {φ : ℝ} (_h0 : 0 ≤ φ) (_h1 : φ < 1) (n : ℕ) :
    |roundDyadic n φ - φ| ≤ 1 / (2 : ℝ) ^ (n + 1) :=
  abs_roundDyadic_sub_le n φ

/-- GrandUnif21 Theorem 7, exponential form: the error is at most `2^{-(n+1)}`
written with a single power. -/
theorem source_theorem7_exp {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < 1) (n : ℕ) :
    |roundDyadic n φ - φ| ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  simpa only [one_div, inv_pow] using abs_roundDyadic_sub_le n φ

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
