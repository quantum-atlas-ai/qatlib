/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators

noncomputable def tvDist {X : Type*} [Fintype X] [DecidableEq X]
    (p q : FinDist X) : ℝ := (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x|

theorem expect_sub_tvDist {X : Type*} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (w : X → ℝ) (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    |p.expect w - q.expect w| ≤ 2 * tvDist p q := by
  have he : p.expect w - q.expect w = ∑ x, (p.prob x - q.prob x) * w x := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    _ = |∑ x, (p.prob x - q.prob x) * w x| := congrArg abs he
    _ ≤ ∑ x, |(p.prob x - q.prob x) * w x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |p.prob x - q.prob x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hw₀ x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hw₁ x)
    _ = _ := by unfold tvDist; ring

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
