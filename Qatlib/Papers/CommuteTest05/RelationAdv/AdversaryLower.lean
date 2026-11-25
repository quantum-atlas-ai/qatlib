/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.RelationAdv

@[expose] public section

/-!
# The composed adversary lower bound of Theorem 2.4.1

The adversary argument of [Itakura2005], Theorem 2.4.1 telescopes the per-query progress of a
weight function `W` and concludes that a positive total change forces a lower bound on the number
of queries. The scalar telescoping step is already available as
`Qatlib.Papers.CommuteTest05.RelationAdv.adversary_query_lower`; this module composes it with the
per-query increment bound `2 * R / sqrt (m * m')` to obtain the paper's stated conclusion
`t ≥ sqrt (m * m') / 16` at the `1 / 4` error convention.

The statement is purely the two-step composition. The state-level reduction that produces `W`
from an adversary relation, and the embedding of a concrete search instance into `m` and `m'`,
are not part of this module.

## Main statements

* `adversary_lower_of_increment`: a total change of at least `R / 8` with per-step increments at
  most `2 * R / sqrt (m * m')` forces `sqrt (m * m') / 16 ≤ t`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.CommuteTest05.RelationAdv

open Qatlib.Papers.CommuteTest05.RelationAdv

/-- Composing the telescoping estimate with the Lemma 18 increment bound yields the adversary
lower bound `sqrt (m * m') / 16 ≤ t` of [Itakura2005], Theorem 2.4.1. -/
theorem adversary_lower_of_increment (W : ℕ → ℝ) (t : ℕ) (m m' R : ℝ)
    (hm : 0 < m) (hm' : 0 < m') (hR : 0 < R)
    (hstep : ∀ j, j < t → |W (j + 1) - W j| ≤ 2 / Real.sqrt (m * m') * R)
    (hchange : R / 8 ≤ |W t - W 0|) :
    Real.sqrt (m * m') / 16 ≤ (t : ℝ) := by
  have hmm' : 0 < m * m' := mul_pos hm hm'
  have hs : 0 < Real.sqrt (m * m') := Real.sqrt_pos.mpr hmm'
  have h := adversary_query_lower W (2 / Real.sqrt (m * m') * R) R t hstep hchange
  have hdiv : (1 : ℝ) / 8 ≤ (t : ℝ) * (2 / Real.sqrt (m * m')) := by
    have h1 : R / 8 / R ≤ ((t : ℝ) * (2 / Real.sqrt (m * m') * R)) / R :=
      div_le_div_of_nonneg_right h hR.le
    have e1 : R / 8 / R = 1 / 8 := by
      field_simp
    have e2 : (t : ℝ) * (2 / Real.sqrt (m * m') * R) / R =
        (t : ℝ) * (2 / Real.sqrt (m * m')) := by
      field_simp
    rwa [e1, e2] at h1
  have hmul := mul_le_mul_of_nonneg_right hdiv hs.le
  have e3 : (t : ℝ) * (2 / Real.sqrt (m * m')) * Real.sqrt (m * m') = 2 * (t : ℝ) := by
    field_simp
  rw [e3] at hmul
  linarith

end Qatlib.Papers.CommuteTest05.RelationAdv
