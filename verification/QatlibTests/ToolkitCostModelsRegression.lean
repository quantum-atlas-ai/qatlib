/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Compose
public import Qatlib.Concepts.CostModels.Budget

@[expose] public section

/-! Algebraic cost checks for the Deutsch-Jozsa profile of one query and two
macro gates, and for the serial consumption cost of a factor recurrence. -/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Compose
open Qatlib.Concepts.CostModels.Budget

namespace QatlibTests.ToolkitCost

/-- A query-only leaf profile: `n` measured queries with every other resource
unmodeled. -/
def queryOnly (n : ℕ) : CostProfile where
  queries := some n
  macroGates := none
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- The leaf profile matching the bootstrap regression's Deutsch-Jozsa word
counts: one oracle query and two matrix macro gates, with elementary gates,
T-count, depth, and width unmodeled. -/
def djLeaf : CostProfile :=
  { queryOnly 1 with macroGates := some 2 }

/-- Echo of the bootstrap `repeated_counts` semantics at the algebra level:
repeating the Deutsch-Jozsa leaf `k` times costs `k` queries and `2 * k`
macro gates. -/
theorem djEchoRepeat (k : ℕ) :
    (treeCost (treeRepeat djLeaf k)).queries = some k ∧
      (treeCost (treeRepeat djLeaf k)).macroGates = some (2 * k) := by
  refine ⟨?_, repeatMacroMul rfl k⟩
  rw [repeatQueryMul rfl k, Nat.one_mul]

/-- Serial composition propagates unmodeled fields: appending two segments
with unmodeled one-qubit counts leaves the composed one-qubit count
unmodeled — `none`, never a fake zero. -/
theorem serialNoneProp : (serial djLeaf djLeaf).oneQ = none := rfl

/-- Independent-parallel composition adds widths and takes the depth
maximum, as fixed by the profile algebra. -/
theorem parInstance (c d : CostProfile) (hc : c.width = some 3)
    (hd : d.width = some 4) (hcd : c.depth = some 5) (hdd : d.depth = some 7) :
    (par c d).width = some 7 ∧ (par c d).depth = some 7 :=
  ⟨parWidthAdd hc hd, parDepthMax hcd hdd⟩

/-- Positive budget instance: the measured Deutsch-Jozsa shape meets an equal
source budget — every constrained slot is matched by its measured count. -/
theorem djBudgetFits : BudgetLe djLeaf djLeaf :=
  budgetLeIntro ⟨1, rfl, Nat.le_refl _⟩ ⟨2, rfl, Nat.le_refl _⟩ trivial trivial
    trivial trivial trivial

/-- A measurement that exceeds the Deutsch-Jozsa budget: the same profile with
three macro gates instead of two. -/
def djOver : CostProfile := { djLeaf with macroGates := some 3 }

/-- Negative budget instance: a measurement with three macro gates violates a
budget constraining them to two — the check reads the measurement, not the
hope. -/
theorem djBudgetFail : ¬ BudgetLe djOver djLeaf := by
  intro h
  have h2 : optLe (some 3) (some 2) := h.2.1
  have ⟨a, he, ha⟩ := h2
  simp at he
  omega

/-- An unmodeled measurement never conforms to a budget constraining queries:
the opaque profile fails the very budget the measured leaf meets. -/
theorem opaqueNoFit : ¬ BudgetLe opaqueProfile djLeaf :=
  budgetNoOpaque rfl

/-- Factor-recursion consumption shape: the query cost of a step segment
followed by two child segments is the sum of the three component query
costs — the algebra-level reading of a prime-factor cost recurrence whose
sub-calls feed a serial step. -/
theorem factorEcho :
    (treeCost (treeOfList [queryOnly 5, queryOnly 2, queryOnly 3])).queries
      = some (5 + 2 + 3) := by
  rw [listQueryFold]
  rfl

/-- Concrete reuse schedule: the second segment's single wire is among the
first segment's two wires, so the composed width is the maximum. -/
theorem reuseInstance :
    (({0, 1} : Finset (Fin 3)) ∪ {1}).card
      = max ({0, 1} : Finset (Fin 3)).card ({1} : Finset (Fin 3)).card :=
  widthReuseMax _ _ (by decide)

/-- Concrete failure of the width maximum without reuse: two one-wire
segments on disjoint wires compose to width two, so the bare maximum rule
would undercount. -/
theorem disjointWidth : ¬ ({0} ∪ {1} : Finset (Fin 2)).card = 1 := by
  decide

end QatlibTests.ToolkitCost
