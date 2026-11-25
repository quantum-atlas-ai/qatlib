/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Cost of a stopped execution

Proposition 6.7 of arXiv:2604.15393v1 uses one realized trajectory
with fixed costs for a policy lookup, receipt of an outcome, and
posterior update. The terminal declaration contributes a fixed cost.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SeqQsdJeong26.Complexity

/-- Charge each measurement step and then charge the terminal declaration once. -/
def onlinePathCost (steps : ℕ) (policy receive update terminal : ℝ) : ℝ :=
  (∑ _ ∈ Finset.range steps, (policy + receive + update)) + terminal

/-- Proposition 6.7. The expected online cost is the expected stopping time
times the common step cost, plus the fixed terminal declaration cost. -/
theorem expected_onlinePathCost {Ω : Type*} [Fintype Ω] (prob : Ω → ℝ)
    (hnorm : ∑ ω, prob ω = 1) (stopping : Ω → ℕ)
    (policy receive update terminal : ℝ) :
    (∑ ω, prob ω * onlinePathCost (stopping ω) policy receive update terminal) =
      (∑ ω, prob ω * (stopping ω : ℝ)) * (policy + receive + update) + terminal := by
  have hcost (ω : Ω) :
      prob ω * onlinePathCost (stopping ω) policy receive update terminal =
        (prob ω * (stopping ω : ℝ)) * (policy + receive + update) + prob ω * terminal := by
    simp only [onlinePathCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_add, ← mul_assoc]
  simp_rw [hcost]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hnorm, one_mul]

end Qatlib.Papers.SeqQsdJeong26.Complexity
