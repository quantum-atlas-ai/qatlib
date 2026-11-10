/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.ShadowModels.ShadowVariance.QuadraticObservableShadows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.ShadowModels.ShadowVariance

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped BigOperators

def freshPovmDensity {m : ℕ} (d : Fin m → ℕ) (ρ : ∀ i, Operator (d i)) : Operator (∏ i, d i) :=
  Matrix.reindex (flatten d) (flatten d) (productMatrix ρ)

def freshPovmKraus {m : ℕ} (d : Fin m → ℕ) {O : Fin m → Type*} [∀ i, Fintype (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ω : ∀ i, O i) : Operator (∏ i, d i) :=
  Matrix.reindex (flatten d) (flatten d)
    (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat))

end Qatlib.Concepts.SdpDuality.ConeSeparation

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics

open Matrix

structure MeasurementCircuit where
  qubits : ℕ
  gates : List FiniteGateCode
  bitTime : ℕ
  peakSpace : ℕ

def MeasurementCircuit.Wellformed (C : MeasurementCircuit) : Prop :=
  finiteWordLegal C.qubits C.gates = true ∧ C.gates.length ≤ C.bitTime ∧
    C.qubits ≤ C.peakSpace

structure SettingPolicy (Y S : Type) where
  choose : (t : ℕ) → (Fin t → Y) → S
  choiceSteps : ℕ

noncomputable def countedOrderStatistic (k : ℕ) (values : List ℝ) : ℝ × ℕ :=
  let s := insertionSortCounted values
  (s.1.getD k 0, s.2)

noncomputable def countedMedianPost (r : ℕ) (v : Fin (2 * r + 1) → ℝ) : ℝ × ℕ :=
  countedOrderStatistic r (List.ofFn v)

structure StatisticsLedger where
  records : ℕ
  gateTotal : ℕ
  bitTimeTotal : ℕ
  peakSpace : ℕ
  settingSteps : ℕ
  comparisons : ℕ

def statisticsLedger (C : MeasurementCircuit) (records settingSteps comparisons postSpace : ℕ) :
    StatisticsLedger where
  records := records
  gateTotal := records * C.gates.length
  bitTimeTotal := records * C.bitTime + settingSteps + comparisons
  peakSpace := max C.peakSpace postSpace
  settingSteps := settingSteps
  comparisons := comparisons

noncomputable def shadowStatisticsRun (n m r : ℕ)
    (O : Matrix (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
    (ω : Fin (2 * r + 1) → Fin m → Fin n → Fin 3 × Bool)
    (C : MeasurementCircuit) (P : SettingPolicy (Fin n → Fin 3 × Bool) (Fin n → Fin 3)) :
    StatisticsLedger × ℝ :=
  let post := countedMedianPost r (fun b => quadraticShadowU n m O (ω b))
  (statisticsLedger C (m * (2 * r + 1)) (m * (2 * r + 1) * P.choiceSteps) post.2 (2 * r + 1),
    post.1)

noncomputable def riskStatisticsRun (r M : ℕ) (samples : Fin (2 * r + 1) → Fin M)
    (C : MeasurementCircuit) (P : SettingPolicy (Fin M) (Fin M)) :
    StatisticsLedger × ℝ :=
  let post := countedMedianPost r (fun b => aeEstimate M (samples b))
  (statisticsLedger C (2 * r + 1) ((2 * r + 1) * P.choiceSteps) post.2 (2 * r + 1), post.1)

end Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics
