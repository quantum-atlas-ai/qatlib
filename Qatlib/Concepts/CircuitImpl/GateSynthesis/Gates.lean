/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GatesDefs
import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCounts

/-!
# Gate-synthesis budget interfaces

This module exposes the Section 8 two-level and primitive-budget inequalities through the public
budget definitions `instructionBudget`, `twoLevelCount`, and `primitiveBudget`. The numerical
accounting follows the elementary-gate synthesis setting of [BarencoEtAl1995].

The endpoint theorems collect the count bounds and identify each interface quantity with its
underlying definition.

## Main statements

* `two_level_count_ledger`: the two-level count inequalities for positive `n`.
* `primitive_budget_ledger`: explicit bounds proportional to `4 ^ n * n ^ 3`.
* `clause14_endpoint` and `walkGoal_endpoint`: bundled bounds and interface equalities.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis

set_option autoImplicit false

/-- For positive `n`, the lower two-level count and the Section 8 count satisfy the stated
comparisons with `4 ^ n`. -/
theorem two_level_count_ledger (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
      reckTwoLevelLower n ≤ section8TwoLevelCount n ∧
      section8TwoLevelCount n ≤ 4 ^ n := by
  have h := clause14_section8_count_ledger n hn
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- For positive `n`, the Section 8 primitive budget lies between `12 * 4 ^ n * n ^ 3` and `7498
* 4 ^ n * n ^ 3`. -/
theorem primitive_budget_ledger (n : ℕ) (hn : 1 ≤ n) :
    12 * 4 ^ n * n ^ 3 ≤ section8PrimitiveBudget n ∧
      section8PrimitiveBudget n ≤ 7498 * 4 ^ n * n ^ 3 :=
  clause14_primitive_budget_bounds n hn

/-- The public instruction budget equals the Section 8 instruction cost. -/
theorem instruction_budget_eq (n : ℕ) : instructionBudget n = section8InstructionCost n := rfl

/-- The public two-level count equals the Section 8 two-level count. -/
theorem two_level_count_eq (n : ℕ) : twoLevelCount n = section8TwoLevelCount n := rfl

/-- The public primitive budget equals the Section 8 primitive budget. -/
theorem primitive_budget_eq (n : ℕ) : primitiveBudget n = section8PrimitiveBudget n := rfl

/-- The two-level count inequalities, primitive-budget bounds, and instruction-budget
identification hold together for the stated ranges of `n`. -/
theorem clause14_endpoint :
    (∀ (n : ℕ), 1 ≤ n → 4 ^ n ≤ 4 * reckTwoLevelLower n ∧
      reckTwoLevelLower n ≤ section8TwoLevelCount n ∧
      section8TwoLevelCount n ≤ 4 ^ n) ∧
    (∀ (n : ℕ), 1 ≤ n → 12 * 4 ^ n * n ^ 3 ≤ section8PrimitiveBudget n ∧
      section8PrimitiveBudget n ≤ 7498 * 4 ^ n * n ^ 3) ∧
    (∀ (n : ℕ), instructionBudget n = section8InstructionCost n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact two_level_count_ledger n hn
  · intro n hn
    exact primitive_budget_ledger n hn
  · intro n
    exact instruction_budget_eq n

/-- The instruction budget, two-level count, and primitive budget agree with their respective
Section 8 definitions for every `n`. -/
theorem walkGoal_endpoint :
    (∀ (n : ℕ), instructionBudget n = section8InstructionCost n) ∧
    (∀ (n : ℕ), twoLevelCount n = section8TwoLevelCount n) ∧
    (∀ (n : ℕ), primitiveBudget n = section8PrimitiveBudget n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact instruction_budget_eq n
  · intro n
    exact two_level_count_eq n
  · intro n
    exact primitive_budget_eq n

end Qatlib.Concepts.CircuitImpl.GateSynthesis
