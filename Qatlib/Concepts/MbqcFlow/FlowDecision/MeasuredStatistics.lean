/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasuredStatistics

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

theorem clause6_complete (E : FinitePOVM O D) (hM : Function.Bijective (povmMeasurementMap E))
    (ρ : Operator D) (hρ : IsDensityOperator ρ) {n k : ℕ} (hn : 0 < n)
    (h : (Fin k → O) → ℝ) (hcount : (distinctTupleCount n k : ℕ) ≠ 0) :
    (∀ (idx : Fin k → Fin n) (hidx : Function.Injective idx) (y : Fin k → O),
        (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
            * (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0)))
          = ∏ t : Fin k, (povmRecordLaw E ρ hρ).prob (y t)) ∧
    (∀ (idx : Fin k → Fin n) (hidx : Function.Injective idx) (g : (Fin k → O) → ℝ),
        (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * g (fun t => ω (idx t)))
          = ∑ y : Fin k → O, (∏ t : Fin k, (povmRecordLaw E ρ hρ).prob (y t)) * g y) ∧
    (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * povmUStatisticK h ω
        = kernelMeanK (povmRecordLaw E ρ hρ) h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro idx hidx y
    exact povm_joint_marginal (povmRecordLaw E ρ hρ) idx hidx y
  · intro idx hidx g
    exact povm_joint_expect (povmRecordLaw E ρ hρ) idx hidx g
  · exact povmUStatisticK_unbiased (povmRecordLaw E ρ hρ) h hcount

theorem clause9_complete (E : FinitePOVM O D) (hM : Function.Bijective (povmMeasurementMap E))
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (A : Fin 2 → Operator D) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    ((povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A 0)) ω)
      = (Matrix.trace (A 0 * ρ)).re) ∧
    ((povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O => (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A 0)) ω
          - (Matrix.trace (A 0 * ρ)).re) ^ 2)
      = (povmRecordLaw E ρ hρ).variance (povmStatistic E hM (A 0)) / n) ∧
    ((povmRecordLaw E ρ hρ).variance (povmStatistic E hM (A 0))
      ≤ ‖povmMomentEffect E hM (A 0)‖) ∧
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A 0)) ω
          - (Matrix.trace (A 0 * ρ)).re|)
      ≤ ‖povmMomentEffect E hM (A 0)‖ / (n * ε ^ 2)) ∧
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O => ∃ i : Fin 2,
          ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A i)) ω
            - (Matrix.trace (A i * ρ)).re|)
      ≤ (‖povmMomentEffect E hM (A 0)‖ + ‖povmMomentEffect E hM (A 1)‖)
          / (n * ε ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact povm_sample_mean_unbiased E hM ρ hρ (A 0) hn
  · exact povm_sample_mean_variance E hM ρ hρ (A 0) hn
  · exact povm_variance_le E hM ρ hρ (A 0)
  · exact povm_sample_confidence_bound E hM ρ hρ (A 0) hn ε hε
  · exact povm_two_observables_shared_records E hM ρ hρ A hn ε hε

theorem thresholdGoal_complete {K : ℕ} (means : List ℚ) (hK : 0 < K) (hlen : means.length = K)
    (history : List (Fin 3 × Fin 2)) :
    (rationalInsertionSortCounted means).1.Perm means ∧
    (rationalInsertionSortCounted means).1.SortedLE ∧
    (∀ j, j < K / 2 →
        (rationalInsertionSortCounted means).1.getD j 0
          ≤ (rationalInsertionSortCounted means).1.getD (K / 2) 0) ∧
    (∀ j, K / 2 < j → j < means.length →
        (rationalInsertionSortCounted means).1.getD (K / 2) 0
          ≤ (rationalInsertionSortCounted means).1.getD j 0) ∧
    (nativeResultDependentAxis [(0, 0), (0, 0)]
      ≠ nativeResultDependentAxis [(0, 1), (0, 0)]) ∧
    (nativeResultDependentAxisCost history ≤ history.length + nativeAxisTable.length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rationalInsertionSortCounted_perm means
  · exact rationalInsertionSortCounted_sorted means
  · exact (rationalInsertionSortCounted_median_property means hK hlen).1
  · exact (rationalInsertionSortCounted_median_property means hK hlen).2
  · exact nativeResultDependentAxis_depends_on_labels
  · exact nativeResultDependentAxisCost_le history

end MeasuredStatistics
end Qatlib.Concepts.MbqcFlow.FlowDecision
