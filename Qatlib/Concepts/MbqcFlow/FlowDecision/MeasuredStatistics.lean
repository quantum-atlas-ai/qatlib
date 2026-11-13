/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs

/-!
# Measured-record statistical guarantees

This module collects product-marginal identities, unbiased kernel averages, and sample-mean
confidence bounds for finite POVM records. For a bijective POVM measurement map,
`clause9_complete` bounds deviations of reconstructed statistics for one observable and for two
observables using shared records.

`thresholdGoal_complete` combines rational insertion-sort and median properties with a concrete
outcome-dependent axis selector and its cost bound. The quantum statistical background is
described in [Holevo1982].

## Main statements

* `clause6_complete`: selected-record product laws and unbiased kernel averages.
* `clause9_complete`: sample-mean, variance, and confidence bounds.
* `thresholdGoal_complete`: sorted-median and adaptive-axis properties.

## References

* [Holevo, 1982][Holevo1982]
-/

open Qatlib.Foundations.PureStateMath
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

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- Distinct positions in the POVM sample record have product marginals and product-law
expectations. Averaging a kernel over injective tuples is unbiased when the number of such
tuples is nonzero. -/
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

/-- For a POVM with bijective measurement map, the reconstructed sample mean is unbiased, its
mean squared error is the single-record variance divided by `n`, and the variance is bounded
by the moment-effect norm. The resulting confidence bounds apply to one observable and to
two observables using the same records. -/
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

/-- Counted insertion sort preserves the rational data, sorts it, and gives the stated median
inequalities. The outcome-dependent axis distinguishes the displayed histories and has cost
at most the history length plus the axis-table length. -/
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
