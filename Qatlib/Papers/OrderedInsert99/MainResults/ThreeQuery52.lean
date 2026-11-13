/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.Exact

/-!
# Necessary conditions for three-query insertion

Records pointwise nonnegativity conditions for a three-query ansatz and a necessary bound for an
exact invariant algorithm at size 52. The result `three_query52_necessary` specializes the
invariant success bound in the setting of [FarhiEtAl1999].

## Main statements

* `three_query52_necessary`: forces `52 ≤ sinSum 52 ^ 6` from an exact three-query invariant
  algorithm.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

/-- The pointwise conditions `0 ≤ 1 + A1 p + B0 p` and `0 ≤ 1 + A1 p` for a three-query ansatz. -/
def ThreeQueryConditions (N : ℕ) (A1 B0 : Fin (2 * N) → ℝ) : Prop :=
  (∀ p, 0 ≤ 1 + A1 p + B0 p) ∧ (∀ p, 0 ≤ 1 + A1 p)

/-- An exact three-query invariant insertion algorithm for size 52 implies `52 ≤ sinSum 52 ^ 6`
[FarhiEtAl1999]. -/
theorem three_query52_necessary (h : ExactInvariantAlgorithm 52 3) :
    (52 : ℝ) ≤ (sinSum 52) ^ 6 := by
  obtain ⟨α, hα⟩ := h
  have hprob := exactStage_prob 52 3 (by norm_num) α hα
  have hb := invariant_success_bound 52 3 (by norm_num) α
  rw [hprob] at hb
  have hm := mul_le_mul_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 52)
  have hcancel : (1 / (52 : ℝ) * (sinSum 52) ^ (2 * 3)) * (52 : ℝ) = (sinSum 52) ^ 6 := by
    field_simp
  norm_num at hcancel ⊢
  linarith

end Qatlib.Papers.OrderedInsert99.MainResults
