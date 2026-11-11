/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Lemma 12 — rounding error at iteration `j`

Source: arXiv:2105.02859v3, Lemma 12 (Sec. V A 2, metadata line 1682) and
Appendix B, Eqs. (B9)--(B10).

If the target phase `φ` needs more than `n` bits, then at the end of iteration
`j ≥ 0` the register holds `θ = 0.r̃_j.φ̃_{j+1}…φ̃_n`, obtained by rounding
`0.φ[j+1:]` to `n-j` binary places, and the rounding error obeys

`|0.r̃_j.φ̃[j+1:] − 0.φ[j+1:]| ≤ 2^{j-n-1}`.

Since `0.φ[j+1:]` is the tail of a phase in `[0,1)`, this is exactly nearest
rounding to `n-j` binary places, whose error is half a unit in the last place,
`2^{-(n-j+1)} = 2^{j-n-1}` (paper's own calculation in Eq. (B9)).

Boundary: the arithmetic error bound; the identification of the QSVT phase
measurement with this rounding is the paper's algorithm model, not formalized.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

/-- GrandUnif21 Lemma 12 (arXiv:2105.02859v3, metadata line 1682): rounding the
tail `x = 0.φ[j+1:] ∈ [0,1)` to `n-j` binary places has error at most
`2^{j-n-1}`, written here as `2^j / 2^{n+1}`. -/
theorem source_lemma12 {x : ℝ} (_h0 : 0 ≤ x) (_h1 : x < 1) {j n : ℕ} (hj : j ≤ n) :
    |roundDyadic (n - j) x - x| ≤ (2 : ℝ) ^ j / (2 : ℝ) ^ (n + 1) := by
  have h := abs_roundDyadic_sub_le (n - j) x
  have hidx : n - j + 1 = n + 1 - j := by omega
  rw [hidx] at h
  refine h.trans_eq ?_
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ j * (2 : ℝ) ^ (n + 1 - j) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega : j ≤ n + 1)]
  rw [hpow]
  have hj0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hj1 : (2 : ℝ) ^ (n + 1 - j) ≠ 0 := by positivity
  field_simp

/-- GrandUnif21 Lemma 12, restated in half-powers: `|θ_j − 0.φ[j+1:]| ≤
(1/2)^{n-j+1}`. -/
theorem source_lemma12_half_pow {x : ℝ} (_h0 : 0 ≤ x) (_h1 : x < 1) {j n : ℕ}
    (hj : j ≤ n) :
    |roundDyadic (n - j) x - x| ≤ (1 / 2 : ℝ) ^ (n - j + 1) := by
  have hidx : n - j + 1 = n + 1 - j := by omega
  simpa only [hidx, one_div, inv_pow] using abs_roundDyadic_sub_le (n - j) x

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
