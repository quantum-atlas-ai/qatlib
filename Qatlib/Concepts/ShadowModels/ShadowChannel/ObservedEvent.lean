/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveQuery.RawProcess.ObservedCircuitLaws

/-!
# Events in observed quantum circuits

`observedEventMass` sums branch masses over observed traces satisfying a Boolean event. The
module proves nonnegativity, monotonicity, complement and label decompositions, and total-mass
bounds for well-formed circuits with a unitary oracle.

Tail estimates relate the mass of branches with many queries to `expectedObservedQueries`. These
estimates bound the accepting mass retained when restricting attention to branches with fewer
than a chosen number of queries. See [NielsenChuang2010] for background.

## Main statements

* `observedEventMass_add_compl`: event and complement masses recover the input mass.
* `observedQueries_tail_le`: a query-count tail bound.
* `observedAcceptance_sub_expected_div_le`: retained acceptance under a query cutoff.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

/-- Pointwise comparison on the members of a list implies comparison of the corresponding real
sums. -/
private theorem sum_map_mono {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Summing a function with zero outside a Boolean event equals summing it over the filtered
list. -/
private theorem event_sum_filter {α : Type*} (xs : List α) (f : α → ℝ)
    (event : α → Bool) :
    (xs.map (fun x => if event x then f x else 0)).sum =
      ((xs.filter event).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : event x <;> simp [hx, ih]

/-- The sums restricted to a Boolean event and its negation add to the unrestricted sum. -/
private theorem event_sum_add_not {α : Type*} (xs : List α) (f : α → ℝ)
    (event : α → Bool) :
    (xs.map (fun x => if event x then f x else 0)).sum +
      (xs.map (fun x => if !event x then f x else 0)).sum = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : event x <;> simp only [List.map_cons, List.sum_cons, hx,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] <;>
      linarith only [ih]

/-- An event-restricted sum splits into its intersection with another event and its intersection
with that event's negation. -/
private theorem event_sum_split {α : Type*} (xs : List α) (f : α → ℝ)
    (event other : α → Bool) :
    (xs.map (fun x => if event x then f x else 0)).sum =
      (xs.map (fun x => if event x && other x then f x else 0)).sum +
      (xs.map (fun x => if event x && !other x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases he : event x <;> cases ho : other x <;>
      simp only [List.map_cons, List.sum_cons, he, ho, Bool.false_and,
        Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, zero_add] <;> linarith only [ih]

/-- Summing event-restricted list sums over every value of a finite label recovers the
unrestricted sum. -/
private theorem sum_label_event {α J : Type*} [Fintype J] [DecidableEq J]
    (xs : List α) (f : α → ℝ) (label : α → J) :
    (∑ j : J, (xs.map (fun x => if label x = j then f x else 0)).sum) =
      (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih]
    simp

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The sum of branch masses of observed circuit traces satisfying the given Boolean event. -/
noncomputable def observedEventMass (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (event : BranchTrace I → Bool) : ℝ :=
  ((observedTraces O program ψ).map
    (fun t => if event t then branchMass t.state else 0)).sum

/-- The mass of every observed event is nonnegative. -/
theorem observedEventMass_nonneg (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (event : BranchTrace I → Bool) :
    0 ≤ observedEventMass O program ψ event := by
  apply List.sum_nonneg
  intro r hr
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
  split_ifs
  · exact branchMass_nonneg t.state
  · exact le_rfl

/-- Implication between events on the observed traces implies the corresponding inequality
between event masses. -/
theorem observedEventMass_mono (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (event other : BranchTrace I → Bool)
    (h : ∀ t ∈ observedTraces O program ψ, event t = true → other t = true) :
    observedEventMass O program ψ event ≤ observedEventMass O program ψ other := by
  apply sum_map_mono
  intro t ht
  by_cases he : event t = true
  · simp [he, h t ht he]
  · by_cases ho : other t = true
    · simpa [he, ho] using branchMass_nonneg t.state
    · have hz : (0 : ℝ) ≤ 0 := le_rfl
      simpa [he, ho] using hz

/-- For a well-formed circuit and a unitary oracle, the event containing every observed trace
has mass equal to the input branch mass. -/
theorem observedEventMass_true (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) :
    observedEventMass O program ψ (fun _ => true) = branchMass ψ := by
  simpa only [observedEventMass, ↓reduceIte] using
    observedTraces_mass O hO program hprogram ψ

/-- The event mass of accepting traces equals the observed acceptance mass. -/
theorem observedEventMass_accepted (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) :
    observedEventMass O program ψ (fun t => t.accepted) = observedAcceptance O program ψ := by
  rw [observedAcceptance_eq_sum]
  exact event_sum_filter _ _ _

/-- For a well-formed circuit and a unitary oracle, the masses of an event and its complement
sum to the input branch mass. -/
theorem observedEventMass_add_compl (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) (event : BranchTrace I → Bool) :
    observedEventMass O program ψ event +
      observedEventMass O program ψ (fun t => !event t) = branchMass ψ := by
  rw [← observedTraces_mass O hO program hprogram ψ]
  exact event_sum_add_not _ _ _

/-- An observed event's mass splits into its intersections with another event and that event's
complement. -/
theorem observedEventMass_split (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (event other : BranchTrace I → Bool) :
    observedEventMass O program ψ event =
      observedEventMass O program ψ (fun t => event t && other t) +
      observedEventMass O program ψ (fun t => event t && !other t) :=
  event_sum_split _ _ _ _

/-- For a well-formed circuit and a unitary oracle, every observed event has mass at most the
input branch mass. -/
theorem observedEventMass_le_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) (ψ : QState I) (event : BranchTrace I → Bool) :
    observedEventMass O program ψ event ≤ branchMass ψ := by
  rw [← observedEventMass_true O hO program hprogram ψ]
  exact observedEventMass_mono O program ψ event (fun _ => true) (by simp)

/-- For a normalized input, a well-formed circuit, and a unitary oracle, every observed event
has mass at most one. -/
theorem observedEventMass_le_one (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (program : ObservedCircuit I)
    (hprogram : observedWellFormed program) {ψ : QState I} (hψ : Normalized ψ)
    (event : BranchTrace I → Bool) : observedEventMass O program ψ event ≤ 1 := by
  simpa only [branchMass, measureProb_univ hψ] using
    observedEventMass_le_mass O hO program hprogram ψ event

/-- For a well-formed circuit and a unitary oracle, summing event masses over all values of a
finite trace label gives the input branch mass. -/
theorem sum_observedEventMass_label {J : Type*} [Fintype J] [DecidableEq J]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (program : ObservedCircuit I) (hprogram : observedWellFormed program)
    (ψ : QState I) (label : BranchTrace I → J) :
    (∑ j : J, observedEventMass O program ψ (fun t => decide (label t = j))) =
      branchMass ψ := by
  rw [← observedTraces_mass O hO program hprogram ψ]
  simpa only [observedEventMass, decide_eq_true_eq] using
    sum_label_event (observedTraces O program ψ) (fun t => branchMass t.state) label

/-- The mass of traces using at least `K` queries, multiplied by `K`, is at most the expected
observed query count. -/
theorem observedQueries_tail_mul_le (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (K : ℕ) :
    (K : ℝ) * observedEventMass O program ψ (fun t => decide (K ≤ t.queries)) ≤
      expectedObservedQueries O program ψ := by
  rw [expectedObservedQueries_eq_sum]
  unfold observedEventMass
  rw [← List.sum_map_mul_left]
  apply sum_map_mono
  intro t _
  by_cases ht : K ≤ t.queries
  · have hcast : (K : ℝ) ≤ (t.queries : ℝ) := by exact_mod_cast ht
    simpa [ht, mul_comm] using mul_le_mul_of_nonneg_left hcast (branchMass_nonneg t.state)
  · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte, mul_zero]
    exact mul_nonneg (branchMass_nonneg t.state) (Nat.cast_nonneg _)

/-- For positive `K`, the mass of traces using at least `K` queries is at most the expected
query count divided by `K`. -/
theorem observedQueries_tail_le (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) {K : ℕ} (hK : 0 < K) :
    observedEventMass O program ψ (fun t => decide (K ≤ t.queries)) ≤
      expectedObservedQueries O program ψ / K := by
  apply (le_div_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)).2
  simpa only [mul_comm] using observedQueries_tail_mul_le O program ψ K

/-- An upper bound `B` on the expected query count gives the tail bound `B/K` at every positive
query threshold `K`. -/
theorem observedQueries_tail_le_of_expected_le (O : Matrix I I ℂ)
    (program : ObservedCircuit I) (ψ : QState I) {K : ℕ} (hK : 0 < K)
    {B : ℝ} (hB : expectedObservedQueries O program ψ ≤ B) :
    observedEventMass O program ψ (fun t => decide (K ≤ t.queries)) ≤ B / K := by
  exact le_trans (observedQueries_tail_le O program ψ hK)
    (div_le_div_of_nonneg_right hB (Nat.cast_nonneg _))

/-- The mass of accepting traces using fewer than `K` queries is at least the total acceptance
mass minus the mass of traces using at least `K` queries. -/
theorem observedAcceptance_sub_tail_le (O : Matrix I I ℂ) (program : ObservedCircuit I)
    (ψ : QState I) (K : ℕ) :
    observedAcceptance O program ψ -
      observedEventMass O program ψ (fun t => decide (K ≤ t.queries)) ≤
      observedEventMass O program ψ (fun t => t.accepted && decide (t.queries < K)) := by
  have hsplit := observedEventMass_split O program ψ (fun t => t.accepted)
    (fun t => decide (K ≤ t.queries))
  have hmono := observedEventMass_mono O program ψ
    (fun t => t.accepted && decide (K ≤ t.queries))
    (fun t => decide (K ≤ t.queries)) (by
      intro t _ ht
      cases hacc : t.accepted <;> simp_all)
  have hnot : (fun t : BranchTrace I => t.accepted && !decide (K ≤ t.queries)) =
      (fun t => t.accepted && decide (t.queries < K)) := by
    funext t
    by_cases ht : K ≤ t.queries
    · simp [ht, Nat.not_lt.mpr ht]
    · simp [ht, Nat.lt_of_not_ge ht]
  rw [observedEventMass_accepted, hnot] at hsplit
  linarith only [hsplit, hmono]

/-- For positive `K`, the accepting mass on traces using fewer than `K` queries is at least
total acceptance minus the expected query count divided by `K`. -/
theorem observedAcceptance_sub_expected_div_le (O : Matrix I I ℂ)
    (program : ObservedCircuit I) (ψ : QState I) {K : ℕ} (hK : 0 < K) :
    observedAcceptance O program ψ - expectedObservedQueries O program ψ / K ≤
      observedEventMass O program ψ (fun t => t.accepted && decide (t.queries < K)) :=
  le_trans (sub_le_sub_left (observedQueries_tail_le O program ψ hK) _)
    (observedAcceptance_sub_tail_le O program ψ K)

end Qatlib.Concepts.ShadowModels.ShadowChannel
