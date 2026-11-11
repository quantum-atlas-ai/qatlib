/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedEvent

/-!
# Query budgets and truncation of observed circuits

`observedQueryBudget` bounds the number of queries on any branch of an observed circuit, and
`truncateObservedQueries` stops execution before exceeding a chosen budget. The module bounds
branchwise and expected query counts and identifies the accepted mass retained by truncation.
These resource bounds use the quantum query model described in [NielsenChuang2010].

## Main statements

* `queries_le_observedQueryBudget`: Every execution trace respects the structural budget.
* `observedAcceptance_truncate_eq`: Truncation retains precisely the accepted mass with query
  count at most the budget.
* `observedAcceptance_sub_expected_le_truncate`: The loss of accepted mass is bounded by the
  expected query count divided by one more than the budget.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*}

/-- Computes the structural query bound of an observed circuit by counting query steps and
taking suprema over measurement continuations. -/
def observedQueryBudget : ObservedCircuit I → ℕ
  | .halt _ => 0
  | .step (.gate _) next => observedQueryBudget next
  | .step .query next => observedQueryBudget next + 1
  | .measure n _ next => Finset.univ.sup (fun o : Fin n => observedQueryBudget (next o))
  | .project _ onFalse onTrue => max (observedQueryBudget onFalse) (observedQueryBudget onTrue)

/-- Truncates an observed circuit to a query budget, rejecting immediately when another query
would exceed the remaining budget. -/
def truncateObservedQueries : ObservedCircuit I → ℕ → ObservedCircuit I
  | .halt accepted, _ => .halt accepted
  | .step (.gate U) next, K => .step (.gate U) (truncateObservedQueries next K)
  | .step .query _, 0 => .halt false
  | .step .query next, K + 1 => .step .query (truncateObservedQueries next K)
  | .measure n label next, K =>
      .measure n label (fun o => truncateObservedQueries (next o) K)
  | .project P onFalse onTrue, K =>
      .project P (truncateObservedQueries onFalse K) (truncateObservedQueries onTrue K)

/-- The structural query budget of a circuit truncated at `K` is at most `K`. -/
theorem observedQueryBudget_truncate_le (program : ObservedCircuit I) (K : ℕ) :
    observedQueryBudget (truncateObservedQueries program K) ≤ K := by
  induction program generalizing K with
  | halt accepted => simp [truncateObservedQueries, observedQueryBudget]
  | step s next ih =>
    cases s with
    | gate U => exact ih K
    | query =>
      cases K with
      | zero => exact le_rfl
      | succ K => exact Nat.add_le_add_right (ih K) 1
  | measure n label next ih =>
    exact Finset.sup_le (fun o _ => ih o K)
  | project P onFalse onTrue ihFalse ihTrue =>
    exact max_le (ihFalse K) (ihTrue K)

/-- Truncating at a budget that already bounds the circuit's structural query budget leaves the
circuit unchanged. -/
theorem truncateObservedQueries_eq_self (program : ObservedCircuit I) {K : ℕ}
    (hK : observedQueryBudget program ≤ K) : truncateObservedQueries program K = program := by
  induction program generalizing K with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate U =>
      change ObservedCircuit.step (.gate U) (truncateObservedQueries next K) = _
      rw [ih hK]
    | query =>
      cases K with
      | zero =>
        have h : observedQueryBudget next + 1 ≤ 0 := hK
        omega
      | succ K =>
        have h : observedQueryBudget next ≤ K := Nat.le_of_succ_le_succ hK
        change ObservedCircuit.step .query (truncateObservedQueries next K) = _
        rw [ih h]
  | measure n label next ih =>
    change ObservedCircuit.measure n label (fun o => truncateObservedQueries (next o) K) = _
    have hn : (fun o => truncateObservedQueries (next o) K) = next := by
      funext o
      have hsup : observedQueryBudget (next o) ≤
          Finset.univ.sup (fun j : Fin n => observedQueryBudget (next j)) :=
        Finset.le_sup (f := fun j : Fin n => observedQueryBudget (next j)) (Finset.mem_univ o)
      exact ih o (le_trans hsup hK)
    rw [hn]
  | project P onFalse onTrue ihFalse ihTrue =>
    change ObservedCircuit.project P (truncateObservedQueries onFalse K)
      (truncateObservedQueries onTrue K) = _
    rw [ihFalse (le_trans (le_max_left _ _) hK),
      ihTrue (le_trans (le_max_right _ _) hK)]

/-- Truncating twice at the same query budget is equivalent to truncating once. -/
theorem truncateObservedQueries_idempotent (program : ObservedCircuit I) (K : ℕ) :
    truncateObservedQueries (truncateObservedQueries program K) K =
      truncateObservedQueries program K :=
  truncateObservedQueries_eq_self _ (observedQueryBudget_truncate_le program K)

variable [Fintype I] [DecidableEq I]

/-- Query truncation preserves well-formedness of an observed circuit. -/
theorem observedWellFormed_truncate (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (K : ℕ) :
    observedWellFormed (truncateObservedQueries program K) := by
  induction program generalizing K with
  | halt accepted => trivial
  | step s next ih =>
    cases s with
    | gate U => exact ⟨hprogram.1, ih hprogram.2 K⟩
    | query =>
      cases K with
      | zero => trivial
      | succ K => exact ih hprogram K
  | measure n label next ih => exact fun o => ih o (hprogram o) K
  | project P onFalse onTrue ihFalse ihTrue =>
    exact ⟨hprogram.1, ihFalse hprogram.2.1 K, ihTrue hprogram.2.2 K⟩

/-- The query count of every observed execution trace is bounded by the circuit's structural
query budget. -/
theorem queries_le_observedQueryBudget (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) {t : BranchTrace I} (ht : t ∈ observedTraces O program ψ) :
    t.queries ≤ observedQueryBudget program := by
  induction program generalizing ψ t with
  | halt accepted =>
    simp only [observedTraces, List.mem_singleton] at ht
    subst t
    exact le_rfl
  | step s next ih =>
    cases s with
    | gate U =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih (ApplyGate U ψ) (t := u) hu
    | query =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact Nat.add_le_add_right (ih (ApplyGate O ψ) (t := u) hu) 1
  | measure n label next ih =>
    obtain ⟨xs, hxs, ht⟩ := List.mem_flatten.mp ht
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact le_trans (ih o _ (t := u) hu)
      (Finset.le_sup (f := fun j : Fin n => observedQueryBudget (next j)) (Finset.mem_univ o))
  | project P onFalse onTrue ihFalse ihTrue =>
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact le_trans (ihFalse _ (t := u) hu) (le_max_left _ _)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact le_trans (ihTrue _ (t := u) hu) (le_max_right _ _)

/-- For a unitary oracle and a well-formed circuit, the expected query count is bounded by the
structural query budget times the input branch mass. -/
theorem expectedObservedQueries_le_structural_mul_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) :
    expectedObservedQueries O program ψ ≤ (observedQueryBudget program : ℝ) * branchMass ψ :=
  expectedObservedQueries_le_budget_mul_mass O hO program hprogram ψ _
    (fun _ ht => queries_le_observedQueryBudget O program ψ ht)

/-- For a normalized input, unitary oracle, and well-formed circuit, the expected query count is
at most the structural query budget. -/
theorem expectedObservedQueries_le_structural (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) :
    expectedObservedQueries O program ψ ≤ observedQueryBudget program :=
  expectedObservedQueries_le_budget O hO program hprogram hψ _
    (fun _ ht => queries_le_observedQueryBudget O program ψ ht)

/-- Every execution trace of a circuit truncated at `K` uses at most `K` queries. -/
theorem queries_truncate_le (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (K : ℕ) {t : BranchTrace I}
    (ht : t ∈ observedTraces O (truncateObservedQueries program K) ψ) : t.queries ≤ K :=
  le_trans (queries_le_observedQueryBudget O _ ψ ht) (observedQueryBudget_truncate_le program K)

/-- For a normalized input, unitary oracle, and well-formed circuit, truncating at `K` bounds
the expected query count by `K`. -/
theorem expectedObservedQueries_truncate_le (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) (K : ℕ) :
    expectedObservedQueries O (truncateObservedQueries program K) ψ ≤ K :=
  expectedObservedQueries_le_budget O hO _ (observedWellFormed_truncate program hprogram K)
    hψ K (fun _ ht => queries_truncate_le O program ψ K ht)

/-- The accepted mass of the truncated execution equals the mass of original traces that accept
and use at most `K` queries. -/
private theorem truncate_accepted_event (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (K : ℕ) (ψ : QState I) :
    observedEventMass O (truncateObservedQueries program K) ψ (fun t => t.accepted) =
      observedEventMass O program ψ (fun t => t.accepted && decide (t.queries ≤ K)) := by
  induction program generalizing K ψ with
  | halt accepted => simp [truncateObservedQueries, observedEventMass, observedTraces]
  | step s next ih =>
    cases s with
    | gate U =>
      simpa only [truncateObservedQueries, observedEventMass, observedTraces,
        List.map_map, Function.comp_def] using ih K (ApplyGate U ψ)
    | query =>
      cases K with
      | zero =>
        simp [truncateObservedQueries, observedEventMass, observedTraces,
          List.map_map, Function.comp_def]
      | succ K =>
        simpa only [truncateObservedQueries, observedEventMass, observedTraces,
          List.map_map, Function.comp_def, Nat.succ_eq_add_one, Nat.add_le_add_iff_right]
          using ih K (ApplyGate O ψ)
  | measure n label next ih =>
    simp only [truncateObservedQueries, observedEventMass, observedTraces,
      List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
      List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro o _
    exact ih o K (Collapse ψ (Finset.univ.filter (fun i => label i = o)))
  | project P onFalse onTrue ihFalse ihTrue =>
    simp only [truncateObservedQueries, observedEventMass, observedTraces,
      List.map_append, List.sum_append, List.map_map, Function.comp_def]
    exact congrArg₂ (fun a b : ℝ => a + b)
      (ihFalse K (ProjectiveBranch P false ψ)) (ihTrue K (ProjectiveBranch P true ψ))

/-- Acceptance mass after truncation at `K` equals the original mass of accepted traces using at
most `K` queries. -/
theorem observedAcceptance_truncate_eq (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (K : ℕ) :
    observedAcceptance O (truncateObservedQueries program K) ψ =
      observedEventMass O program ψ (fun t => t.accepted && decide (t.queries ≤ K)) := by
  rw [← observedEventMass_accepted]
  exact truncate_accepted_event O program K ψ

/-- Truncating an observed circuit cannot increase its acceptance mass. -/
theorem observedAcceptance_truncate_le (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (K : ℕ) :
    observedAcceptance O (truncateObservedQueries program K) ψ ≤ observedAcceptance O program ψ := by
  rw [observedAcceptance_truncate_eq, ← observedEventMass_accepted O program ψ]
  apply observedEventMass_mono
  intro t _ ht
  cases ha : t.accepted
  · simp [ha] at ht
  · rfl

/-- Truncation at `K` retains at least the original acceptance mass minus the expected query
count divided by `K + 1`. -/
theorem observedAcceptance_sub_expected_le_truncate (O : Matrix I I ℂ)
    (program : ObservedCircuit I) (ψ : QState I) (K : ℕ) :
    observedAcceptance O program ψ - expectedObservedQueries O program ψ / (K + 1 : ℕ) ≤
      observedAcceptance O (truncateObservedQueries program K) ψ := by
  rw [observedAcceptance_truncate_eq]
  simpa only [Nat.lt_succ_iff] using
    observedAcceptance_sub_expected_div_le O program ψ (Nat.succ_pos K)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
