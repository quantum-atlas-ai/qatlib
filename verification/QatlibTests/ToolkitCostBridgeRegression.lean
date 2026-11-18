/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Compose
public import Qatlib.Concepts.CostModels.Budget
public import Qatlib.Concepts.CostModels.CountBridge

@[expose] public section

/-! The counting bridge from query words to measured cost profiles.
`wordProfile` reads
`QueryCount` / `GateCount` off the public Deutsch-Jozsa word, so the
bootstrap regressions `query_and_macro_counts` and `repeated_counts` become
profile equalities, and the `CompileCert` contract is instantiated on a real
compiled word with its negative controls. Counts remain query-word counts
(oracle queries and matrix macro gates); no elementary-gate, T-count, depth,
or width model is claimed. -/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Compose
open Qatlib.Concepts.CostModels.Budget
open Qatlib.Concepts.CostModels.CountBridge

namespace QatlibTests.ToolkitCostBridge

/-- The measured profile of the Deutsch-Jozsa word: one oracle query and two
matrix macro gates, with every elementary-level field unmodeled. This is the
count regression `query_and_macro_counts` lifted to profiles. -/
theorem djProfileEq (n : ℕ) :
    wordProfile (djCircuit n)
      = { queries := some 1, macroGates := some 2, oneQ := none, twoQ := none,
          tCount := none, depth := none, width := none } := by
  simp [wordProfile, djCircuit]

/-- Repetition bridge lifting the bootstrap `repeated_counts`: `k` copies of
the Deutsch-Jozsa word measure `k` queries and `2 * k` macro gates. -/
theorem djRepeatEq (n k : ℕ) :
    (wordProfile (RepeatCircuit (djCircuit n) k)).queries = some k ∧
    (wordProfile (RepeatCircuit (djCircuit n) k)).macroGates = some (2 * k) := by
  have hQ : QueryCount (djCircuit n) = 1 := by simp [djCircuit]
  have hG : GateCount (djCircuit n) = 2 := by simp [djCircuit]
  rw [profRepeatQ, profRepeatM, hQ, hG]
  exact ⟨by simp, by rw [Nat.mul_comm k 2]⟩

/-- Repeating the measured
Deutsch-Jozsa profile inside a cost tree yields the same `k` queries and
`2 * k` macro gates as the public repeated word. -/
theorem djTreeEq (n k : ℕ) :
    (treeCost (treeRepeat (wordProfile (djCircuit n)) k)).queries = some k ∧
    (treeCost (treeRepeat (wordProfile (djCircuit n)) k)).macroGates = some (2 * k) := by
  refine ⟨?_, ?_⟩
  · rw [repeatBridgeQ]
    simp [djCircuit]
  · rw [repeatBridgeM]
    simp [djCircuit, Nat.mul_comm]

/-- The source budget matching the Deutsch-Jozsa measured profile: one query
and two macro gates, with no constraint on the unmodeled fields. -/
def djBudget : CostProfile where
  queries := some 1
  macroGates := some 2
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- A positive compilation certificate on a real compiled word: the product
is the Deutsch-Jozsa word itself, its measured profile fits the equal
budget, and the final query bound is read back off the measured product via
`certQueryBound`, never off the budget alone. -/
theorem djCert (n : ℕ) :
    ∃ cert : CompileCert (wordProfile : Circuit (Reg n × Bool) → CostProfile) djBudget,
      cert.out = djCircuit n ∧
      ∃ a, (wordProfile cert.out).queries = some a ∧ a ≤ 1 := by
  have hfits : BudgetLe (wordProfile (djCircuit n)) djBudget := by
    rw [djProfileEq]
    exact budgetLeIntro ⟨1, rfl, Nat.le_refl _⟩ ⟨2, rfl, Nat.le_refl _⟩
      trivial trivial trivial trivial trivial
  refine ⟨⟨djCircuit n, hfits⟩, rfl, ?_⟩
  exact certQueryBound (CompileCert.mk (djCircuit n) hfits) rfl

/-- A budget that constrains the unmodeled one-qubit gate count to zero. -/
def djOneQZero : CostProfile := { djBudget with oneQ := some 0 }

/-- Negative control: no certificate can meet a budget constraining the
one-qubit count, because the word profile never models that field — an
unmodeled measurement never satisfies a constrained slot (`optLeNoneNeg`). -/
theorem djNoOneQZero (n : ℕ) :
    ¬ Nonempty (CompileCert (wordProfile : Circuit (Reg n × Bool) → CostProfile)
      djOneQZero) := by
  rintro ⟨cert⟩
  have h3 : optLe (wordProfile cert.out).oneQ (some 0) := cert.fits.2.2.1
  exact optLeNoneNeg h3

/-- The measured Deutsch-Jozsa profile is not the all-zero empty profile:
the unmodeled fields keep "not modeled" distinguishable from a measured
zero. -/
theorem djNotEmpty (n : ℕ) : wordProfile (djCircuit n) ≠ emptyProfile := by
  intro h
  have h1 : (wordProfile (djCircuit n)).oneQ = emptyProfile.oneQ := congrArg _ h
  simp [wordProfile, emptyProfile] at h1

end QatlibTests.ToolkitCostBridge
