/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatisticsDefs
import Qatlib.Concepts.ShadowModels.SampleBudget.QuadraticShadowSourceParametersHuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalQuan
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.ShadowModels.ShadowVariance

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics

set_option autoImplicit false

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open scoped Classical
set_option warningAsError false

theorem thresholdGoal :

  (∀ (n m r : ℕ) (O : Matrix (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      (ω : Fin (2 * r + 1) → Fin m → Fin n → Fin 3 × Bool),
    (quadraticShadowMedianCounted n m r O ω).1 = quadraticShadowMedian n m r O ω ∧
      (quadraticShadowMedianCounted n m r O ω).2.1 = 2 * r + 1 ∧
      (quadraticShadowMedianCounted n m r O ω).2.2 ≤ (2 * r + 1) ^ 2) ∧

  (∀ (Y S : Type) (P : SettingPolicy Y S) (C : MeasurementCircuit) (records : ℕ),
    (statisticsLedger C records (records * P.choiceSteps) 0 0).settingSteps =
        records * P.choiceSteps ∧
      (statisticsLedger C records (records * P.choiceSteps) 0 0).bitTimeTotal =
        records * C.bitTime + records * P.choiceSteps) ∧

  (∀ (n m r : ℕ) (O : Matrix (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      (ω : Fin (2 * r + 1) → Fin m → Fin n → Fin 3 × Bool)
      (C : MeasurementCircuit) (P : SettingPolicy (Fin n → Fin 3 × Bool) (Fin n → Fin 3)),
    C.Wellformed →
      (shadowStatisticsRun n m r O ω C P).2 = quadraticShadowMedian n m r O ω ∧
        (shadowStatisticsRun n m r O ω C P).1.records = m * (2 * r + 1) ∧
        (shadowStatisticsRun n m r O ω C P).1.gateTotal =
          (m * (2 * r + 1)) * C.gates.length ∧
        (shadowStatisticsRun n m r O ω C P).1.settingSteps =
          (m * (2 * r + 1)) * P.choiceSteps ∧
        (shadowStatisticsRun n m r O ω C P).1.comparisons ≤ (2 * r + 1) ^ 2 ∧
        (shadowStatisticsRun n m r O ω C P).1.bitTimeTotal =
          (m * (2 * r + 1)) * C.bitTime + (m * (2 * r + 1)) * P.choiceSteps +
            (shadowStatisticsRun n m r O ω C P).1.comparisons ∧
        (shadowStatisticsRun n m r O ω C P).1.peakSpace = max C.peakSpace (2 * r + 1)) ∧

  (∀ (r M : ℕ) (samples : Fin (2 * r + 1) → Fin M) (C : MeasurementCircuit)
      (P : SettingPolicy (Fin M) (Fin M)),
    C.Wellformed →
      (riskStatisticsRun r M samples C P).2 = meanMedian r M samples ∧
        (riskStatisticsRun r M samples C P).1.records = 2 * r + 1 ∧
        (riskStatisticsRun r M samples C P).1.gateTotal =
          (2 * r + 1) * C.gates.length ∧
        (riskStatisticsRun r M samples C P).1.settingSteps =
          (2 * r + 1) * P.choiceSteps ∧
        (riskStatisticsRun r M samples C P).1.comparisons ≤ (2 * r + 1) ^ 2 ∧
        (riskStatisticsRun r M samples C P).1.bitTimeTotal =
          (2 * r + 1) * C.bitTime + (2 * r + 1) * P.choiceSteps +
            (riskStatisticsRun r M samples C P).1.comparisons ∧
        (riskStatisticsRun r M samples C P).1.peakSpace = max C.peakSpace (2 * r + 1)) ∧

  (∀ (k : ℕ) (values : List ℝ),
    (countedOrderStatistic k values).2 = (insertionSortCounted values).2 ∧
      (countedOrderStatistic k values).2 ≤ values.length * values.length ∧
      ∀ (r : ℕ) (v : Fin (2 * r + 1) → ℝ),
        (countedMedianPost r v).1 = sortedBlockMedian r v ∧
          (countedMedianPost r v).2 ≤ (2 * r + 1) ^ 2) ∧

  (∀ (C : MeasurementCircuit) (records settingSteps comparisons postSpace : ℕ),
    C.Wellformed →
      finiteWordLegal C.qubits C.gates = true ∧
        C.gates.length ≤ C.bitTime ∧ C.qubits ≤ C.peakSpace ∧
        (statisticsLedger C records settingSteps comparisons postSpace).gateTotal =
          records * C.gates.length ∧
        (statisticsLedger C records settingSteps comparisons postSpace).bitTimeTotal =
          records * C.bitTime + settingSteps + comparisons ∧
        C.peakSpace ≤ (statisticsLedger C records settingSteps comparisons postSpace).peakSpace ∧
        postSpace ≤ (statisticsLedger C records settingSteps comparisons postSpace).peakSpace) ∧

  QuadraticShadowSourceParametersSubgoal ∧ ReadoutMedianFiniteSubgoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact quadraticShadowMedianCounted_spec
  · intro _Y _S P C records
    exact ⟨rfl, rfl⟩
  · intro n m r O ω C P _hC
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    change (insertionSortCounted (List.ofFn fun b => quadraticShadowU n m O (ω b))).2 ≤
      (2 * r + 1) ^ 2
    simpa only [List.length_ofFn, pow_two] using!
      insertionSortCounted_cost_le (List.ofFn fun b => quadraticShadowU n m O (ω b))
  · intro r M samples C P _hC
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    change (insertionSortCounted (List.ofFn fun b => aeEstimate M (samples b))).2 ≤
      (2 * r + 1) ^ 2
    simpa only [List.length_ofFn, pow_two] using!
      insertionSortCounted_cost_le (List.ofFn fun b => aeEstimate M (samples b))
  · intro k values
    refine ⟨rfl, ?_, ?_⟩
    · change (insertionSortCounted values).2 ≤ values.length * values.length
      exact insertionSortCounted_cost_le values
    · intro r v
      refine ⟨rfl, ?_⟩
      change (insertionSortCounted (List.ofFn v)).2 ≤ (2 * r + 1) ^ 2
      simpa only [List.length_ofFn, pow_two] using!
        insertionSortCounted_cost_le (List.ofFn v)
  · intro C records settingSteps comparisons postSpace hC
    refine ⟨hC.1, hC.2.1, hC.2.2, rfl, rfl, ?_, ?_⟩
    · change C.peakSpace ≤ max C.peakSpace postSpace
      exact Nat.le_max_left C.peakSpace postSpace
    · change postSpace ≤ max C.peakSpace postSpace
      exact Nat.le_max_right C.peakSpace postSpace
  · exact ⟨quadraticShadowSourceParametersSubgoal, riskReadoutMedianFinite⟩

end Qatlib.Papers.ClassShadows20.LowerBound
