/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 10 (propagation of the relative solution error to the Riccati variable)

Source: arXiv:2404.07303, §5.1.1, Lemma 10, (5.22)–(5.34), pages 37–38.

If `‖x − x̂‖ ≤ ε₁‖x‖` (5.22), then `‖y − ŷ‖ ≤ ε` with
`ε = 2ε₁(1 + 1/‖y‖ + 1/‖u‖)` (5.24).  The proof bounds `‖P(x+w) − P(x̂+w)‖` by
`ε₁(1 + 1/‖y‖ + 1/‖u‖)‖u‖` (5.25)–(5.29) using `‖w‖ = 1`, `y = u v⁻¹`, then splits the
normalised-state difference (5.30)–(5.34).

Fully proved here: the coefficient identity `ε = 2ε₁(1+1/‖y‖+1/‖u‖)` and the final step
`e ≤ 2δ ⇒ e ≤ ε` from the source's derived bound `δ ≤ ε₁(1+1/‖y‖+1/‖u‖)`.  The norm
estimates (5.25)–(5.29) and the normalised-state stability (5.30)–(5.34) are recorded in
the headline statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

/-- `ε = 2ε₁(1 + 1/‖y‖ + 1/‖u‖)` of (5.24). -/
def lemma10Eps (ε1 yNorm uNorm : ℝ) : ℝ :=
  2 * ε1 * (1 + 1 / yNorm + 1 / uNorm)

/-- Lemma10Eps nonneg: the paper model identity or bound. -/
theorem lemma10Eps_nonneg (ε1 yNorm uNorm : ℝ) (hε1 : 0 ≤ ε1)
    (hy : 0 < yNorm) (hu : 0 < uNorm) :
    0 ≤ lemma10Eps ε1 yNorm uNorm := by
  unfold lemma10Eps
  have : 0 ≤ 1 + 1 / yNorm + 1 / uNorm := by positivity
  positivity

/-- **Lemma 10, (5.29) ⇒ (5.24).**  From the derived bound
`δ ≤ ε₁(1 + 1/‖y‖ + 1/‖u‖)` and the triangle split factor `2` of (5.32), the solution
error satisfies `e ≤ ε` with `ε = lemma10Eps ε₁ ‖y‖ ‖u‖`. -/
theorem lemma10_error_le_eps (ε1 δ e yNorm uNorm : ℝ) (hε1 : 0 ≤ ε1)
    (hy : 0 < yNorm) (hu : 0 < uNorm)
    (hδ : δ ≤ ε1 * (1 + 1 / yNorm + 1 / uNorm))
    (he : e ≤ 2 * δ) :
    e ≤ lemma10Eps ε1 yNorm uNorm := by
  unfold lemma10Eps
  linarith

/-- **Lemma 10, headline (5.22)–(5.24).**  Relative error `ε₁` in `x` gives
`‖y − ŷ‖ ≤ ε` with the componentwise bound (5.24).

Lean gap: the source works with the vectors `x = (u,v)`, `w`, the projections `P`, and
the matrix relation `y = u v⁻¹`; this requires the concrete block-vector model plus the
normalised-state stability estimate (5.30)–(5.34).  Candidate reuse: the generic
normalised-vector bound `‖a/‖a‖ − b/‖b‖‖ ≤ 2‖a−b‖/‖a‖` (not in Mathlib; prove by hand
from the reverse triangle inequality).  Handoff: instantiate `lemma10_error_le_eps` with
`δ = ε₁(1+1/‖y‖+1/‖u‖)‖u‖/‖u‖` after proving (5.29) from `u = y v`, `v = y⁻¹u`. -/
theorem lemma10_relative_error (ε1 xNorm xhatNorm yErr yNorm uNorm : ℝ)
    (hε1 : 0 ≤ ε1) (hy : 0 < yNorm) (hu : 0 < uNorm)
    (hx : |xNorm - xhatNorm| ≤ ε1 * xNorm)
    (hxy : yErr ≤ 2 * ε1 * (1 + 1 / yNorm + 1 / uNorm)) :
    yErr ≤ lemma10Eps ε1 yNorm uNorm := by
  unfold lemma10Eps
  linarith

end Qatlib.Papers.QuadHamilton24.MainResults
