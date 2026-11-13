/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.CircuitCompile.VariableKrausDefs

/-!
# Statistics preserved by Kraus padding

Padding a `VariableKrausCircuit` to a common outcome bound preserves sums of branch statistics
that vanish on zero-state branches, after restoring the original outcome records. This supplies
a finite circuit representation compatible with the Kraus description of quantum operations in
[Kraus1971].

The general statistic identity specializes to event masses and expected oracle-query counts;
these statements require that each instrument fits the chosen bound.

## Main statements

* `variableKraus_padding_statistic`: preserve zero-state-vanishing branch statistics.
* `variableKraus_padding_event`: preserve events on restored outcome records.
* `variableKraus_padding_expected`: preserve expected query counts.

## References

* [Kraus, 1971][Kraus1971]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.CircuitCompile

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- If all instruments fit the common outcome bound `S`, padding preserves the sum of any branch
statistic that vanishes on zero-state traces, after restoring each padded outcome record. -/
theorem variableKraus_padding_statistic {d : ℕ} (O : Operator d)
    (P : VariableKrausCircuit d) (S : ℕ) (hfit : variableKrausFits S P)
    (rho : Operator d) (F : MixedBranchTrace d → ℝ)
    (hzero : ∀ (b : Bool) (q g m : ℕ) (rec : List (ℕ × ℕ)),
      F ⟨0, b, q, g, m, rec⟩ = 0) :
    ((krausCircuitMixedTraces O (padVariableKraus S P) rho).map
      (fun t => F {t with outcomes := restoreVariableKrausRecord P t.outcomes})).sum =
    ((variableKrausMixedTraces O P rho).map F).sum := by
  classical
  induction P generalizing rho F with
  | halt accepted => rfl
  | step action next ih =>
      cases action with
      | gate G =>
          have hh := ih hfit (conjBranch G rho)
            (fun t => F {t with gates := t.gates + 1})
            (fun b q g m rec => hzero b q (g+1) m rec)
          simpa only [padVariableKraus, krausCircuitMixedTraces,
            variableKrausMixedTraces, restoreVariableKrausRecord,
            List.map_map, Function.comp_def] using hh
      | query =>
          have hh := ih hfit (conjBranch O rho)
            (fun t => F {t with queries := t.queries + 1})
            (fun b q g m rec => hzero b (q+1) g m rec)
          simpa only [padVariableKraus, krausCircuitMixedTraces,
            variableKrausMixedTraces, restoreVariableKrausRecord,
            List.map_map, Function.comp_def] using hh
  | instrument s K next ih =>
      rcases hfit with ⟨hs,hchildren⟩
      let f : Fin s → ℝ := fun a =>
        ((variableKrausMixedTraces O (next a) (conjBranch (K a) rho)).map
          (fun t => F {t with gates := t.gates+2, measurements := t.measurements+1, outcomes := (s,a.val)::t.outcomes})).sum
      simp only [padVariableKraus, krausCircuitMixedTraces, variableKrausMixedTraces,
        List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        List.map_map, Function.comp_def]
      change _ = ∑ a : Fin s, f a
      rw [← sum_fin_zero_padding hs f]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.val < s
      · simp only [dif_pos ha]
        have hh := ih ⟨a.val,ha⟩ (hchildren ⟨a.val,ha⟩)
          (conjBranch (K ⟨a.val,ha⟩) rho)
          (fun t => F {t with gates := t.gates+2, measurements := t.measurements+1, outcomes := (s,a.val)::t.outcomes})
          (fun b q g m rec => hzero b q (g+2) (m+1) ((s,a.val)::rec))
        simpa only [f, restoreVariableKrausRecord, dif_pos ha] using hh
      · simp only [dif_neg ha, conjBranch_apply, Matrix.zero_mul,
          Matrix.mul_zero, krausCircuitMixedTraces, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          restoreVariableKrausRecord]
        exact hzero false 0 2 1 []

/-- Padding a variable Kraus circuit preserves every event mass depending on acceptance and the
restored outcome record, provided its instruments fit `S`. -/
theorem variableKraus_padding_event {d : ℕ} (O : Operator d)
    (P : VariableKrausCircuit d) (S : ℕ) (hfit : variableKrausFits S P)
    (rho : Operator d) (E : Bool → List (ℕ × ℕ) → Bool) :
    krausCircuitEventMass O (padVariableKraus S P) rho
      (fun b rec => E b (restoreVariableKrausRecord P rec)) =
    variableKrausEventMass O P rho E := by
  classical
  simpa [krausCircuitEventMass, variableKrausEventMass, mixedMass] using
    (variableKraus_padding_statistic O P S hfit rho
      (fun t => if E t.accepted t.outcomes then (Matrix.trace t.state).re else 0)
      (by intro b q g m rec; simp))

/-- Padding a variable Kraus circuit to a fitting common outcome bound preserves its expected
number of oracle queries. -/
theorem variableKraus_padding_expected {d : ℕ} (O : Operator d)
    (P : VariableKrausCircuit d) (S : ℕ) (hfit : variableKrausFits S P)
    (rho : Operator d) :
    krausCircuitExpectedQueries O (padVariableKraus S P) rho =
    variableKrausExpectedQueries O P rho := by
  classical
  simpa [krausCircuitExpectedQueries, variableKrausExpectedQueries, mixedMass] using
    (variableKraus_padding_statistic O P S hfit rho
      (fun t => (Matrix.trace t.state).re * (t.queries : ℝ))
      (by intro b q g m rec; simp))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
