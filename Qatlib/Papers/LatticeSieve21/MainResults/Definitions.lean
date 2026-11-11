/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeSieve21 / MainResults / Definitions — caps, filters, `V_d(α)` and `θ_α^*`

Fixed paper version: arXiv:2105.05608v1 (12 May 2021), André Chailloux and
Johanna Loyer, *Lattice sieving via quantum random walks*.

This file records the geometric objects that the paper's probabilistic
statements (Propositions 5--9, Lemmas 1--2, Corollary 1) are about:

* the `α`-cap (hypercone) `H_{s,α} = {v : θ(v,s) ≤ α}` around a centre `s`
  (Section 3, p.5);
* the cap ratio `V_d(α) := poly(d)·sin^d(α)` (p.5, line 402), the fraction of
  the sphere covered by an `α`-cap.  As in the paper, the `poly(d)` factor is
  absorbed into `o(1)` terms and only the exponential factor `sin^d α` is kept;
* the residual threshold `θ_α^* := 2·arcsin(1/(2 sin α))` of Corollary 1
  (p.7), and the predicate "the pair is reducing" (`θ(x₀,x₁) ≤ π/3`, p.7).

All statements are phrased in an arbitrary real inner-product space; the paper
works with the unit sphere of `ℝ^d`, which is the case of interest.
-/

set_option autoImplicit false
noncomputable section

open Real

namespace Qatlib.Papers.LatticeSieve21.MainResults.Definitions

open InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `α`-cap (hypercone) around a centre `s`: `H_{s,α} = {v : θ(v,s) ≤ α}`
(Section 3, p.5, before Proposition 5). -/
def cap (s : E) (α : ℝ) : Set E := {v | angle v s ≤ α}

/-- `V_d(α) = poly(d)·sin^d(α)`: the fraction of the unit sphere covered by an
`α`-cap (p.5, line 402).  The `poly(d)` factor is kept inside the paper's
`o(1)` terms, so the recorded exponential factor is `sin^d α`. -/
def V (d α : ℝ) : ℝ := Real.sin α ^ d

/-- `V_d(α)` is nonnegative for cap angles `α ∈ [0, π]` and any real exponent
`d` (p.5). -/
theorem V_nonneg {α : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ Real.pi) (d : ℝ) : 0 ≤ V d α := by
  unfold V
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ) d

/-- `V_d(α)` is strictly positive when `α ∈ (0, π)` (p.5). -/
theorem V_pos {α : ℝ} (h0 : 0 < α) (hπ : α < Real.pi) (d : ℝ) : 0 < V d α := by
  unfold V
  exact Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi h0 hπ) d

/-- The residual threshold `θ_α^* := 2·arcsin(1/(2 sin α))` (Corollary 1, p.7). -/
def thetaStar (α : ℝ) : ℝ := 2 * Real.arcsin (1 / (2 * Real.sin α))

/-- A pair of vectors in the same `α`-filter bucket is *reducing* when
`θ(x₀,x₁) ≤ π/3`, equivalently `‖x₀ - x₁‖ ≤ 1` for unit vectors (p.7). -/
def Reduces (x₀ x₁ : E) : Prop := angle x₀ x₁ ≤ Real.pi / 3

end Qatlib.Papers.LatticeSieve21.MainResults.Definitions
