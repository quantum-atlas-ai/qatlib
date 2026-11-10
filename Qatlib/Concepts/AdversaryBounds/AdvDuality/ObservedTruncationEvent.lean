/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Mathlib.Tactic.Linarith
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem observed_event_short_le_truncate (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) (K : ℕ) (E : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass O P psi
        (fun t => E t.accepted t.outcomes && decide (t.queries ≤ K)) ≤
      observedEventMass O (truncateObservedQueries P K) psi
        (fun t => E t.accepted t.outcomes) := by
  induction P generalizing psi K E with
  | halt accepted =>
    simp [truncateObservedQueries, observedEventMass, observedTraces]
  | step s next ih =>
    cases s with
    | gate U =>
      simpa only [truncateObservedQueries, observedEventMass, observedTraces,
        List.map_map, Function.comp_def] using ih (ApplyGate U psi) K E
    | query =>
      cases K with
      | zero =>
        calc
          observedEventMass O (.step .query next) psi
              (fun t => E t.accepted t.outcomes && decide (t.queries ≤ 0)) = 0 := by
            simp [observedEventMass, observedTraces, List.map_map, Function.comp_def]
          _ ≤ observedEventMass O (truncateObservedQueries (.step .query next) 0) psi
              (fun t => E t.accepted t.outcomes) :=
            observedEventMass_nonneg O _ psi _
      | succ K =>
        simpa only [truncateObservedQueries, observedEventMass, observedTraces,
          List.map_map, Function.comp_def, Nat.succ_eq_add_one,
          Nat.add_le_add_iff_right] using ih (ApplyGate O psi) K E
  | measure n label next ih =>
    simp only [truncateObservedQueries, observedEventMass, observedTraces,
      List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
      List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_le_sum
    intro o _
    simpa only [observedEventMass] using
      ih o (Collapse psi (Finset.univ.filter (fun i => label i = o))) K
        (fun accepted outcomes => E accepted ((n, o.val) :: outcomes))
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [truncateObservedQueries, observedEventMass, observedTraces,
      List.map_append, List.sum_append, List.map_map, Function.comp_def]
    apply add_le_add
    · simpa only [observedEventMass] using
        ihFalse (ProjectiveBranch M false psi) K
          (fun accepted outcomes => E accepted ((2, 0) :: outcomes))
    · simpa only [observedEventMass] using
        ihTrue (ProjectiveBranch M true psi) K
          (fun accepted outcomes => E accepted ((2, 1) :: outcomes))

theorem observed_event_sub_expected_le_truncate (O : Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState I) (K : ℕ)
    (E : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass O P psi (fun t => E t.accepted t.outcomes) -
        expectedObservedQueries O P psi / (K + 1 : ℕ) ≤
      observedEventMass O (truncateObservedQueries P K) psi
        (fun t => E t.accepted t.outcomes) := by
  have hsplit := observedEventMass_split O P psi
    (fun t => E t.accepted t.outcomes) (fun t => decide (t.queries ≤ K))
  have hlong :
      observedEventMass O P psi
          (fun t => E t.accepted t.outcomes && !decide (t.queries ≤ K)) ≤
        observedEventMass O P psi (fun t => decide (K + 1 ≤ t.queries)) := by
    apply observedEventMass_mono
    intro t _ ht
    by_cases hq : t.queries ≤ K
    · simp [hq] at ht
    · have hq' : K + 1 ≤ t.queries := Nat.succ_le_of_lt (Nat.lt_of_not_ge hq)
      simp [hq']
  have htail :
      observedEventMass O P psi (fun t => decide (K + 1 ≤ t.queries)) ≤
        expectedObservedQueries O P psi / (K + 1 : ℕ) :=
    observedQueries_tail_le O P psi (Nat.succ_pos K)
  have hshort := observed_event_short_le_truncate O P psi K E
  linarith only [hsplit, hlong, htail, hshort]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
