/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Lemma 11 — the inner loop computes the tail bits

Source: arXiv:2105.02859v3, Lemma 11 (Sec. V A 2, metadata line 1648) and
Appendix B, Eqs. (B2)--(B9).

The paper's phase-estimation routine starts from `θ = 0` at the last digit and
runs the halving iteration `θ ← φ_{j+1}/2 + θ/2` for `j = n-1, …, 0`.  Lemma 11
states that at the end of iteration `j` the register holds
`θ = 0.φ_{j+1}φ_{j+2}…φ_n`, the contiguous tail of the binary expansion.

The statements below identify the abstract recursion `thetaIter` of
`SourceModel` with the tail fractions `tailFrac`, and record the closed form
`θ_j = 2^j (φ − 0.φ_1…φ_j)` of Eq. (B9) plus the one-step update rule actually
executed by the algorithm.

Boundary: arithmetic content of Lemma 11 only; the QSVT realization of the
`θ ← φ/2 + θ/2` step (the controlled rotation on the phase register) is not
modelled here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

/-- GrandUnif21 Lemma 11 (arXiv:2105.02859v3, Sec. V A 2, metadata line 1648):
if `φ = 0.φ₁…φₙ` is an `n`-bit number, then at the end of iteration `j ≥ 0`
the value produced by the halving iteration is the binary fraction of the
remaining digits, `θ_j = 0.φ_{j+1}…φₙ = 0.φ[j+1:]`. -/
theorem source_lemma11 (φ : ℕ → Bool) {j n : ℕ} (hj : j ≤ n) :
    thetaIter φ n (n - j) = tailFrac φ j n := by
  have hjj : n - (n - j) = j := by omega
  rw [thetaIter_eq_tailFrac φ n (n - j) (by omega), hjj]

/-- GrandUnif21 Lemma 11, closed form (Appendix B, Eq. (B9)): the value at the
end of iteration `j` is `2^j` times the remainder of the phase after its first
`j` digits, `θ_j = 2^j (φ − 0.φ₁…φ_j)`. -/
theorem source_lemma11_closed_form (φ : ℕ → Bool) {j n : ℕ} (hj : j ≤ n) :
    thetaIter φ n (n - j) = (2 : ℝ) ^ j * (binFrac φ n - binFrac φ j) :=
  thetaIter_eq φ hj

/-- GrandUnif21 Lemma 11, one-step update rule (Appendix B, Eqs. (B2)--(B6)):
the value at iteration `j` is the `(j+1)`-st digit over two plus half of the
value at iteration `j+1`. -/
theorem source_lemma11_step (φ : ℕ → Bool) {j n : ℕ} (hj : j < n) :
    thetaIter φ n (n - j) =
      bitVal φ (j + 1) / 2 + thetaIter φ n (n - (j + 1)) / 2 := by
  rw [source_lemma11 φ hj.le, tailFrac_recurrence φ hj, source_lemma11 φ (by omega)]

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
