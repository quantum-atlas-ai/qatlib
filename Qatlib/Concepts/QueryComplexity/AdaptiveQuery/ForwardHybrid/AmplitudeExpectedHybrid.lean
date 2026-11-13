/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardHybrid.PaidCoarse.AdaptiveHybrid
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Hybrid bounds from expected adaptive query counts

This module proves recursive identities, nonnegativity, and the zero input law for
`mixedExpectedQueries`. It then bounds changes in bounded statistics of observation records
under replacement of one unitary oracle by another.

The theorem `amplitude_record_expected_hybrid` uses the expected query count under the first
oracle, multiplied by the operator norm of the oracle difference. It refines the usual query
hybrid comparison underlying [BennettEtAl1997].

## Main statements

* `amplitude_expected_queries_query`: a query contributes the input trace mass plus the
  continuation cost.
* `amplitude_record_expected_hybrid`: an oracle comparison controlled by the expected number of
  queries.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid

open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-- A halting observed circuit has zero mixed expected query count. -/
theorem amplitude_expected_queries_halt (O : Qatlib.Foundations.PureStateMath.Operator d) (accepted : Bool)
    (rho : Qatlib.Foundations.PureStateMath.Operator d) : Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.halt accepted) rho = 0 := by
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces]

/-- A gate step contributes no queries and passes its conjugated input to the continuation's
expected query count. -/
theorem amplitude_expected_queries_gate (O G : Qatlib.Foundations.PureStateMath.Operator d)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.step (.gate G) P) rho =
      Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G rho) := by
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_map, Function.comp_def,
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- Incrementing every trace query count adds the total trace mass to the mass weighted query
sum. -/
private theorem sum_query_increment (l : List (Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d)) :
    (l.map fun t => Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass t * ((t.queries : ℝ) + 1)).sum =
      (l.map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass).sum + (l.map fun t => Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass t * t.queries).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- For a unitary oracle and a well formed continuation, a query step adds the real input trace
to the continuation's mixed expected query count on the oracle conjugated input. -/
theorem amplitude_expected_queries_query (O : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.step .query P) rho =
      (trace rho).re + Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O rho) := by
  calc
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.step .query P) rho =
        ((Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O rho)).map
          fun t => Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass t * ((t.queries : ℝ) + 1)).sum := by
      simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_map, Function.comp_def,
        Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass, Nat.cast_add, Nat.cast_one]
    _ = ((Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O rho)).map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass).sum +
        Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O rho) := sum_query_increment _
    _ = (trace rho).re + Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O rho) := by
      rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_mass_sum O hO P hP,
          Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary O hO]

/-- The mixed expected query count of a partition measurement is the sum of the continuation
costs on its unnormalized projected inputs. -/
theorem amplitude_expected_queries_measure (O : Qatlib.Foundations.PureStateMath.Operator d) (n : ℕ)
    (label : Fin d → Fin n) (next : Fin n → Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d))
    (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.measure n label next) rho =
      ∑ o : Fin n, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (next o)
        (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) rho) := by
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- The mixed expected query count of a projective branch is the sum of the false and true
continuation costs on their respective conjugated inputs. -/
theorem amplitude_expected_queries_project (O Q : Qatlib.Foundations.PureStateMath.Operator d)
    (onFalse onTrue : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O (.project Q onFalse onTrue) rho =
      Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho) +
      Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho) := by
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- The mixed expected query count is nonnegative on positive semidefinite inputs. -/
theorem amplitude_expected_queries_nonneg (O : Qatlib.Foundations.PureStateMath.Operator d)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (rho : Qatlib.Foundations.PureStateMath.Operator d) (hrho : rho.PosSemidef) :
    0 ≤ Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P rho := by
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_leaf_correspondence O P rho).1,
    List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_nonneg fun i _ => ?_
  apply mul_nonneg
  · exact (RCLike.nonneg_iff.mp
      ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch (Qatlib.Concepts.ShadowModels.ShadowChannel.observedLeaf O P i).operator).positive
        hrho).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- The mixed expected query count vanishes on the zero input operator. -/
theorem amplitude_expected_queries_zero (O : Qatlib.Foundations.PureStateMath.Operator d)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) : Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries O P 0 = 0 := by
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries, (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_leaf_correspondence O P 0).1,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_eq_zero
  intro i _
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.leafMixedTrace,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- For a well formed observed circuit on a positive semidefinite input and a record statistic
in `[0, 1]`, replacing unitary oracle `U` by `V` changes its expectation by at most `‖U -
V‖` times the mixed expected query count under `U`. -/
theorem amplitude_record_expected_hybrid {d : ℕ}
    (U V : Qatlib.Foundations.PureStateMath.Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P)
    (rho : Qatlib.Foundations.PureStateMath.Operator d) (hrho : rho.PosSemidef)
    (f : List (ℕ × ℕ) → ℝ) (hf : ∀ h, 0 ≤ f h ∧ f h ≤ 1) :
    |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U P rho f -
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V P rho f| ≤
      ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U P rho := by
  induction P generalizing rho f with
  | halt accepted =>
    simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces,
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.amplitude_expected_queries_halt]
  | step s next ih =>
    cases s with
    | gate G =>
      rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_gate, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_gate,
        Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.amplitude_expected_queries_gate]
      exact ih hP.2 (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G rho)
        ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch G).positive hrho) f hf
    | query =>
      rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_query, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_query]
      have hi := ih hP (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho)
        ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch U).positive hrho) f hf
      have hq :
          |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho) f -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V rho) f| ≤
          ‖U - V‖ * (trace rho).re := by
        rw [abs_sub_comm]
        simpa only [norm_sub_rev] using!
          Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observed_record_query_error V U hV hU next hP rho hrho f hf
      calc
        _ ≤ |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho) f -
                Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho) f| +
              |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho) f -
                Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V rho) f| :=
          abs_sub_le _ _ _
        _ ≤ ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U rho) +
              ‖U - V‖ * (trace rho).re := add_le_add hi hq
        _ = ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U (.step .query next) rho := by
          rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.amplitude_expected_queries_query U hU next hP]
          ring
  | measure n label next ih =>
    rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_measure, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_measure,
      ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ o : Fin n,
          |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U (next o)
              (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) rho)
              (fun h => f ((n, o.val) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V (next o)
              (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) rho)
              (fun h => f ((n, o.val) :: h))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ o : Fin n, ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U (next o)
          (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) rho) := by
        apply Finset.sum_le_sum
        intro o _
        exact ih o (hP o) _
          ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch
            (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o))).positive hrho)
          (fun h => f ((n, o.val) :: h)) (fun h => hf _)
      _ = ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U (.measure n label next) rho := by
        rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.amplitude_expected_queries_measure, Finset.mul_sum]
  | project Q onFalse onTrue ihFalse ihTrue =>
    rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_project, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_project]
    have hiF := ihFalse hP.2.1 (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho)
      ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch (1 - Q)).positive hrho)
      (fun h => f ((2, 0) :: h)) (fun h => hf _)
    have hiT := ihTrue hP.2.2 (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho)
      ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch Q).positive hrho)
      (fun h => f ((2, 1) :: h)) (fun h => hf _)
    calc
      _ ≤ |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho)
                (fun h => f ((2, 0) :: h)) -
              Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho)
                (fun h => f ((2, 0) :: h))| +
            |Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho)
                (fun h => f ((2, 1) :: h)) -
              Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho)
                (fun h => f ((2, 1) :: h))| := by
        convert! abs_add_le
          (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho)
              (fun h => f ((2, 0) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho)
              (fun h => f ((2, 0) :: h)))
          (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho)
              (fun h => f ((2, 1) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho)
              (fun h => f ((2, 1) :: h))) using 1
        abel
      _ ≤ ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) rho) +
            ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q rho) :=
        add_le_add hiF hiT
      _ = ‖U - V‖ * Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedExpectedQueries U (.project Q onFalse onTrue) rho := by
        rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.amplitude_expected_queries_project, mul_add]

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid
