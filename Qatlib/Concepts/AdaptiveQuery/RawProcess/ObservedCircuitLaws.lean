/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Mass and query bounds for observed circuits

This module expresses observed acceptance and expected queries as weighted sums over branch
traces. For well-formed circuits with unitary queries, total branch mass is conserved;
normalized inputs therefore give probability and expected-query bounds. For background, see
[NielsenChuang2010].

## Main statements

* `observedTraces_mass`: For a well-formed observed circuit and a unitary oracle, the sum of all
  terminal branch masses equals the initial branch mass.
* `observedAcceptance_le_one`: For a normalized input, a well-formed observed circuit with a
  unitary oracle has acceptance probability at most one.
* `expectedObservedQueries_le_maximum`: For a normalized input, a well-formed observed circuit
  with a unitary oracle has expected query count at most its maximum observed query count.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

namespace Qatlib.Concepts.AdaptiveQuery.RawProcess

/-- Folding addition of the weights `f` over a list equals the initial accumulator plus the sum
of the mapped weights. -/
private theorem foldl_weight {α : Type*} (f : α → ℝ) (xs : List α) (a : ℝ) :
    xs.foldl (fun total x => total + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- Filtering a list cannot increase the sum of nonnegative weights. -/
private theorem filter_weight_le {α : Type*} (f : α → ℝ) (p : α → Bool)
    (hf : ∀ x, 0 ≤ f x) (xs : List α) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x = true
    · simpa [List.filter_cons, h] using add_le_add_left ih (f x)
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      linarith [hf x]

/-- If all list weights are nonnegative and every query count is at most `K`, their weighted
query sum is at most `K` times their total weight. -/
private theorem weighted_queries_le {α : Type*} (f : α → ℝ) (q : α → ℕ)
    (hf : ∀ x, 0 ≤ f x) (xs : List α) (K : ℕ)
    (hK : ∀ x ∈ xs, q x ≤ K) :
    (xs.map (fun x => f x * q x)).sum ≤ (K : ℝ) * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : (q x : ℝ) ≤ K := by exact_mod_cast hK x List.mem_cons_self
    have htail := ih (fun y hy => hK y (List.mem_cons_of_mem x hy))
    have hmul := mul_le_mul_of_nonneg_left hx (hf x)
    simp only [List.map_cons, List.sum_cons]
    nlinarith

/-- A fold taking successive maxima bounds both its initial value and the value of `q` on every
list element. -/
private theorem foldl_max_ge {α : Type*} (q : α → ℕ) (xs : List α) :
    ∀ a : ℕ, a ≤ xs.foldl (fun n x => max n (q x)) a ∧
      ∀ x ∈ xs, q x ≤ xs.foldl (fun n y => max n (q y)) a := by
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    have htail := ih (max a (q x))
    refine ⟨le_trans (le_max_left _ _) htail.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (le_max_right _ _) htail.1
    · exact htail.2 y hy

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Observed acceptance is the sum of the branch masses of accepted traces. -/
theorem observedAcceptance_eq_sum (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) : observedAcceptance O program ψ =
      (((observedTraces O program ψ).filter (fun t => t.accepted)).map
        (fun t => branchMass t.state)).sum := by
  simp only [observedAcceptance, foldl_weight, zero_add]

/-- Expected observed queries are the sum of each trace query count weighted by its branch mass. -/
theorem expectedObservedQueries_eq_sum (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) : expectedObservedQueries O program ψ =
      ((observedTraces O program ψ).map (fun t => branchMass t.state * t.queries)).sum := by
  simp only [expectedObservedQueries, foldl_weight, zero_add]

/-- For a well-formed observed circuit and a unitary oracle, the sum of all terminal branch
masses equals the initial branch mass. -/
theorem observedTraces_mass (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    : ∀ (program : ObservedCircuit I), observedWellFormed program → ∀ (ψ : QState I),
      ((observedTraces O program ψ).map (fun t => branchMass t.state)).sum = branchMass ψ := by
  intro program
  induction program with
  | halt accepted => intro _ ψ; simp [observedTraces]
  | step s next ih =>
    intro hprogram ψ
    cases s with
    | gate U =>
      simpa [observedTraces, branchMass, List.map_map, Function.comp_def,
        measureProb_applyGate_univ hprogram.1] using
        ih hprogram.2 (ApplyGate U ψ)
    | query =>
      simpa [observedTraces, branchMass, List.map_map, Function.comp_def,
        measureProb_applyGate_univ hO] using ih hprogram (ApplyGate O ψ)
  | measure n label next ih =>
    intro hprogram ψ
    simp only [observedTraces, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, List.map_ofFn, List.sum_ofFn]
    have hnext (o : Fin n) := ih o (hprogram o)
    simp only [hnext]
    exact sum_measureProb_collapse_partition ψ label
  | project P onFalse onTrue ihFalse ihTrue =>
    intro hprogram ψ
    simpa only [observedTraces, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, ihFalse hprogram.2.1, ihTrue hprogram.2.2] using!
      projectiveBranchMass_add hprogram.1 ψ

/-- For a normalized input, a well-formed observed circuit with a unitary oracle has total
terminal branch mass one. -/
theorem observedTraces_mass_eq_one (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) :
    ((observedTraces O program ψ).map (fun t => branchMass t.state)).sum = 1 := by
  rw [observedTraces_mass O hO program hprogram, branchMass, measureProb_univ hψ]

/-- Observed acceptance is nonnegative. -/
theorem observedAcceptance_nonneg (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) : 0 ≤ observedAcceptance O program ψ := by
  simp only [observedAcceptance, foldl_weight, zero_add]
  exact List.sum_nonneg (by
    intro r hr
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
    exact branchMass_nonneg t.state)

/-- For a well-formed observed circuit with a unitary oracle, acceptance mass is at most the
initial branch mass. -/
theorem observedAcceptance_le_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) :
    observedAcceptance O program ψ ≤ branchMass ψ := by
  rw [← observedTraces_mass O hO program hprogram ψ]
  simpa only [observedAcceptance, foldl_weight, zero_add] using
    filter_weight_le (fun t : BranchTrace I => branchMass t.state) (fun t => t.accepted)
      (fun t => branchMass_nonneg t.state) (observedTraces O program ψ)

/-- For a normalized input, a well-formed observed circuit with a unitary oracle has acceptance
probability at most one. -/
theorem observedAcceptance_le_one (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) :
    observedAcceptance O program ψ ≤ 1 := by
  simpa only [branchMass, measureProb_univ hψ] using
    observedAcceptance_le_mass O hO program hprogram ψ

/-- The expected observed query count is nonnegative. -/
theorem expectedObservedQueries_nonneg (O : Matrix I I ℂ)
    (program : ObservedCircuit I) (ψ : QState I) :
    0 ≤ expectedObservedQueries O program ψ := by
  simp only [expectedObservedQueries, foldl_weight, zero_add]
  exact List.sum_nonneg (by
    intro r hr
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
    exact mul_nonneg (branchMass_nonneg t.state) (Nat.cast_nonneg _))

/-- If every trace uses at most `K` queries, a well-formed observed circuit with a unitary
oracle has expected query count at most `K` times the initial branch mass. -/
theorem expectedObservedQueries_le_budget_mul_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) (K : ℕ)
    (hK : ∀ t ∈ observedTraces O program ψ, t.queries ≤ K) :
    expectedObservedQueries O program ψ ≤ (K : ℝ) * branchMass ψ := by
  rw [← observedTraces_mass O hO program hprogram ψ]
  simpa only [expectedObservedQueries, foldl_weight, zero_add] using
    weighted_queries_le (fun t : BranchTrace I => branchMass t.state) (fun t => t.queries)
      (fun t => branchMass_nonneg t.state) (observedTraces O program ψ) K hK

/-- For a normalized input, a uniform bound of `K` queries on every trace bounds the expected
query count by `K` for a well-formed circuit with a unitary oracle. -/
theorem expectedObservedQueries_le_budget (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) (K : ℕ)
    (hK : ∀ t ∈ observedTraces O program ψ, t.queries ≤ K) :
    expectedObservedQueries O program ψ ≤ K := by
  simpa only [branchMass, measureProb_univ hψ, mul_one] using
    expectedObservedQueries_le_budget_mul_mass O hO program hprogram ψ K hK

/-- Every observed trace query count is at most `maximumObservedQueries`. -/
theorem queries_le_maximumObservedQueries (O : Matrix I I ℂ)
    (program : ObservedCircuit I) (ψ : QState I) {t : BranchTrace I}
    (ht : t ∈ observedTraces O program ψ) :
    t.queries ≤ maximumObservedQueries O program ψ :=
  (foldl_max_ge (fun t : BranchTrace I => t.queries) (observedTraces O program ψ) 0).2 t ht

/-- For a normalized input, a well-formed observed circuit with a unitary oracle has expected
query count at most its maximum observed query count. -/
theorem expectedObservedQueries_le_maximum (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ) :
    expectedObservedQueries O program ψ ≤ maximumObservedQueries O program ψ :=
  expectedObservedQueries_le_budget O hO program hprogram hψ _
    (fun _ ht => queries_le_maximumObservedQueries O program ψ ht)

end Qatlib.Concepts.AdaptiveQuery.RawProcess
