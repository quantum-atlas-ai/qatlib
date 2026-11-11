/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceNormalizeError — Lemma 7 (normalized-vector error)

Fixed source: arXiv:2508.15170 (DissipDESolve25), Lemma 7, Equation (34), page 14.

Statement (paper): for two non-zero vectors `x` and `y`,
```
‖ |x⟩ - |y⟩ ‖ ≤ 2 * ‖x - y‖ / ‖x‖ .
```

Here `|x⟩ = NormedSpace.normalize x = x / ‖x‖`. The paper's proof (their Eq. (35))
is the triangle-inequality split
```
‖x/‖x‖ - y/‖y‖‖ ≤ ‖x - y‖/‖x‖ + |‖x‖ - ‖y‖|/‖x‖ ≤ 2‖x - y‖/‖x‖ ,
```
using the reverse triangle inequality. The paper only assumes `x, y ≠ 0`.

A restricted form is already in the shared library:
`QuantumAlgorithm.Papers.QSingValue19.QsVtStability.normalize_error_of_gap`
covers the case `‖x - y‖ < ‖x‖` (it additionally needs the formal normalization gap
so that `normalize y` is guaranteed non-zero).  The present theorem removes that
extra hypothesis by treating the complementary regime `‖x‖ ≤ ‖x - y‖` with the
crude bound `‖normalize y - normalize x‖ ≤ 2 ≤ 2‖x - y‖/‖x‖`, so it matches the
paper statement exactly.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Papers.DissipDESolve25.MainResults.SourceNormalizeError

/-- Fixed arXiv:2508.15170 (DissipDESolve25), Lemma 7, Eq. (34), p.14.
For any two non-zero real-normed vectors `x` and `y`, the normalized vectors satisfy
`‖normalize y - normalize x‖ ≤ 2 ‖x - y‖ / ‖x‖`. No normalization-gap hypothesis
is required; the proof combines the shared `normalize_error_of_gap` with the crude
`≤ 2` bound in the complementary regime. -/
theorem lemma7_normalize_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  by_cases hgap : ‖x - y‖ < ‖x‖
  · -- Main regime: reuse the shared postselection lemma on the normalization gap.
    have h := (normalize_error_of_gap (E := E) (x := x) (y := y)
      (η := ‖x - y‖) (by rw [norm_sub_rev]) hgap).2
    exact h
  · -- Complementary regime `‖x‖ ≤ ‖x - y‖`: both sides are at least the trivial 2-bound.
    rw [not_lt] at hgap
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hn1 : ‖NormedSpace.normalize y‖ = 1 := NormedSpace.norm_normalize hy
    have hn2 : ‖NormedSpace.normalize x‖ = 1 := NormedSpace.norm_normalize hx
    have hle : ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 := by
      calc
        _ ≤ ‖NormedSpace.normalize y‖ + ‖NormedSpace.normalize x‖ := norm_sub_le _ _
        _ = 2 := by rw [hn1, hn2]; norm_num
    have hrhs : 2 ≤ 2 * ‖x - y‖ / ‖x‖ := by
      rw [le_div_iff₀ hxpos]
      nlinarith [hgap, hxpos.le]
    exact le_trans hle hrhs

end Qatlib.Papers.DissipDESolve25.MainResults.SourceNormalizeError
