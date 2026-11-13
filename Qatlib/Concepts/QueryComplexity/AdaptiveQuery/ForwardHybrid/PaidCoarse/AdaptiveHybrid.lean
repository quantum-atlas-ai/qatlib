/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardHybrid.PaidCoarse.ObservedRisk
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalControlledCopy

/-!
# Oracle hybrid bounds for adaptive record statistics

This module gives recursion formulas for `observedRecordExpectation` through gates, queries, and
measurements. It uses trace norm stability to compare the effect of different unitary queries on
positive semidefinite inputs.

The theorem `observed_record_oracle_hybrid` bounds the change of any record statistic valued in
`[0, 1]` by the query budget times the operator norm difference and input trace mass. This is an
adaptive record version of the hybrid comparison used in [BennettEtAl1997].

## Main statements

* `observed_record_query_error`: a bound for changing a single query before a fixed
  continuation.
* `observed_record_oracle_hybrid`: a bound for replacing the oracle throughout an observed
  circuit.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-- A gate step passes its conjugated input to the continuation without changing the record
statistic. -/
theorem recordExpectation_gate (O G : Qatlib.Foundations.PureStateMath.Operator d) (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d))
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (f : List (ℕ × ℕ) → ℝ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O (.step (.gate G) P) ρ f =
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G ρ) f := by
  simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_map, Function.comp_def,
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- A query step passes the oracle conjugated input to the continuation without changing the
record statistic. -/
theorem recordExpectation_query (O : Qatlib.Foundations.PureStateMath.Operator d) (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d))
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (f : List (ℕ × ℕ) → ℝ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O (.step .query P) ρ f =
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O ρ) f := by
  simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_map, Function.comp_def,
    Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- A partition measurement splits the record expectation into a sum over projected inputs,
prefixing each outcome to its continuation record. -/
theorem recordExpectation_measure (O : Qatlib.Foundations.PureStateMath.Operator d) (n : ℕ) (label : Fin d → Fin n)
    (next : Fin n → Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (ρ : Qatlib.Foundations.PureStateMath.Operator d)
    (f : List (ℕ × ℕ) → ℝ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O (.measure n label next) ρ f =
      ∑ o : Fin n, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O (next o)
        (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) ρ)
        (fun h => f ((n, o.val) :: h)) := by
  simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- A projective measurement splits the record expectation into false and true branches,
prefixing the corresponding binary outcome to each continuation record. -/
theorem recordExpectation_project (O Q : Qatlib.Foundations.PureStateMath.Operator d)
    (onFalse onTrue : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (ρ : Qatlib.Foundations.PureStateMath.Operator d)
    (f : List (ℕ × ℕ) → ℝ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O (.project Q onFalse onTrue) ρ f =
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ)
        (fun h => f ((2, 0) :: h)) +
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ)
        (fun h => f ((2, 1) :: h)) := by
  simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]

/-- The real traces of all partition projected inputs sum to the real trace of the original
input. -/
private theorem measurement_input_mass (O : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (n : ℕ) (label : Fin d → Fin n)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    ∑ o : Fin n,
      (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) ρ)).re =
      (trace ρ).re := by
  have hm := Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_mass_sum O hO (.measure n label (fun _ => .halt false))
    (fun _ => trivial) ρ
  simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def] using! hm

/-- For an orthogonal projector, the real traces of its complementary projected inputs sum to
the real trace of the original input. -/
private theorem binary_input_mass (O Q : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (hQ : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector Q)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ)).re + (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ)).re = (trace ρ).re := by
  have hm := Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_mass_sum O hO (.project Q (.halt false) (.halt false))
    ⟨hQ, trivial, trivial⟩ ρ
  simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass, List.map_append, List.sum_append,
    List.map_map, Function.comp_def] using! hm

/-- For a fixed well formed continuation with unitary oracle `U`, replacing its input
conjugation by `U` with conjugation by unitary `V` changes a record statistic in `[0, 1]` by
at most `‖U - V‖` times the positive semidefinite input's real trace. -/
theorem observed_record_query_error (U V : Qatlib.Foundations.PureStateMath.Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef)
    (f : List (ℕ × ℕ) → ℝ) (hf : ∀ h, 0 ≤ f h ∧ f h ≤ 1) :
    |observedRecordExpectation U P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U ρ) f -
        Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ) f|
      ≤ ‖U - V‖ * (trace ρ).re := by
  have hb := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observed_record_input_error U hU P hP (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U ρ) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ)
    ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch U).positive hρ)
    ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch V).positive hρ)
    (by rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary U hU, Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary V hV]) f hf
  have hc : traceNorm (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U ρ - Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ) ≤
      2 * ‖U - V‖ * (trace ρ).re := by
    simpa only [Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch_apply, Qatlib.Concepts.HspRecovery.SieveLaw.posSemidef_traceNorm_eq_re hρ] using!
      Qatlib.Concepts.FreshCopyExec.QpeConsumers.numeric_conjugation_error U V ρ hU hV
  linarith

/-- For a well formed observed circuit on a positive semidefinite input, replacing unitary
oracle `U` by `V` changes a record statistic in `[0, 1]` by at most `observedQueryBudget P *
‖U - V‖` times the real input trace. -/
theorem observed_record_oracle_hybrid (U V : Qatlib.Foundations.PureStateMath.Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef)
    (f : List (ℕ × ℕ) → ℝ) (hf : ∀ h, 0 ≤ f h ∧ f h ≤ 1) :
    |observedRecordExpectation U P ρ f - Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V P ρ f|
      ≤ (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget P : ℝ) * ‖U - V‖ * (Matrix.trace ρ).re := by
  induction P generalizing ρ f with
  | halt accepted =>
    simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces, Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget]
  | step s next ih =>
    cases s with
    | gate G =>
      rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_gate, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_gate]
      simpa only [Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget, Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary G hP.1] using!
        ih hP.2 (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G ρ) ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch G).positive hρ) f hf
    | query =>
      rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_query, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_query]
      have hi := ih hP (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ)
        ((Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch V).positive hρ) f hf
      rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary V hV] at hi
      have hq :=
          Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observed_record_query_error U V hU hV next hP ρ hρ f hf
      calc
        _ ≤ |observedRecordExpectation U next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch U ρ) f -
                Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ) f| +
              |observedRecordExpectation U next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ) f -
                Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V next (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch V ρ) f| := abs_sub_le _ _ _
        _ ≤ ‖U - V‖ * (trace ρ).re +
              (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget next : ℝ) * ‖U - V‖ * (trace ρ).re := add_le_add hq hi
        _ = _ := by simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget, Nat.cast_add, Nat.cast_one]; ring
  | measure n label next ih =>
    rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_measure, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_measure, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ o : Fin n, |observedRecordExpectation U (next o)
              (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) ρ)
              (fun h => f ((n, o.val) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V (next o)
              (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) ρ)
              (fun h => f ((n, o.val) :: h))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ o : Fin n, (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.measure n label next) : ℝ) *
            ‖U - V‖ *
              (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o)) ρ)).re := by
        apply Finset.sum_le_sum
        intro o _
        have hp := (Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch
          (Qatlib.Foundations.InstrumentCore.Measurement.Projector (Finset.univ.filter fun i => label i = o))).positive hρ
        have hb : (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (next o) : ℝ) ≤
            Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.measure n label next) := by
          exact_mod_cast Finset.le_sup
            (f := fun j : Fin n => Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (next j)) (Finset.mem_univ o)
        exact (ih o (hP o) _ hp _ (fun h => hf _)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
            (RCLike.nonneg_iff.mp hp.trace_nonneg).1)
      _ = _ := by rw [← Finset.mul_sum, measurement_input_mass U hU]
  | project Q onFalse onTrue ihFalse ihTrue =>
    rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_project, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.recordExpectation_project]
    have hpF :=
        (Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch (1 - Q)).positive hρ
    have hpT :=
        (Qatlib.Concepts.AdaptiveCP.BranchTrace.completelyPositive_conjBranch Q).positive hρ
    have hiF := ihFalse hP.2.1 _ hpF (fun h => f ((2, 0) :: h)) (fun h => hf _)
    have hiT := ihTrue hP.2.2 _ hpT (fun h => f ((2, 1) :: h)) (fun h => hf _)
    have hbF : (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onFalse : ℝ) ≤
        Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.project Q onFalse onTrue) := by
      exact_mod_cast le_max_left (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onFalse) (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onTrue)
    have hbT : (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onTrue : ℝ) ≤
        Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.project Q onFalse onTrue) := by
      exact_mod_cast le_max_right (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onFalse) (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget onTrue)
    calc
      _ ≤ |observedRecordExpectation U onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ)
                (fun h => f ((2, 0) :: h)) -
              Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ)
                (fun h => f ((2, 0) :: h))| +
            |observedRecordExpectation U onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ)
                (fun h => f ((2, 1) :: h)) -
              Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ)
                (fun h => f ((2, 1) :: h))| := by
        convert! abs_add_le
          (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ) (fun h => f ((2, 0) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onFalse (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ) (fun h => f ((2, 0) :: h)))
          (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation U onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ) (fun h => f ((2, 1) :: h)) -
            Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation V onTrue (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ) (fun h => f ((2, 1) :: h))) using 1
        abel
      _ ≤ (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.project Q onFalse onTrue) : ℝ) * ‖U - V‖ *
            (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (1 - Q) ρ)).re +
          (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedQueryBudget (.project Q onFalse onTrue) : ℝ) * ‖U - V‖ *
            (trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch Q ρ)).re := by
        exact add_le_add (hiF.trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbF (norm_nonneg _))
            (RCLike.nonneg_iff.mp hpF.trace_nonneg).1)) (hiT.trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbT (norm_nonneg _))
            (RCLike.nonneg_iff.mp hpT.trace_nonneg).1))
      _ = _ := by rw [← mul_add, binary_input_mass U Q hU hP.1]

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse
