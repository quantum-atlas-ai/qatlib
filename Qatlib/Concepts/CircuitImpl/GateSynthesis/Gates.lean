/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GatesDefs
import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCounts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis

set_option autoImplicit false

theorem two_level_count_ledger (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
      reckTwoLevelLower n ≤ section8TwoLevelCount n ∧
      section8TwoLevelCount n ≤ 4 ^ n := by
  have h := clause14_section8_count_ledger n hn
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem primitive_budget_ledger (n : ℕ) (hn : 1 ≤ n) :
    12 * 4 ^ n * n ^ 3 ≤ section8PrimitiveBudget n ∧
      section8PrimitiveBudget n ≤ 7498 * 4 ^ n * n ^ 3 :=
  clause14_primitive_budget_bounds n hn

theorem instruction_budget_eq (n : ℕ) : instructionBudget n = section8InstructionCost n := rfl

theorem two_level_count_eq (n : ℕ) : twoLevelCount n = section8TwoLevelCount n := rfl

theorem primitive_budget_eq (n : ℕ) : primitiveBudget n = section8PrimitiveBudget n := rfl

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
