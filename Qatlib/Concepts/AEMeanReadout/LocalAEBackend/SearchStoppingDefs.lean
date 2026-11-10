/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem12K2WindowQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Quan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Quan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem6HeuristicQuan
import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalAngleSubgoalTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalConstantsSubgoalTigh
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstruction
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumFairBitProducer
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem5ApproximateCountingQuan
import Qatlib.Concepts.AmplitudeSearch.Amplification.SearchStoppingDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open Qatlib.Concepts.SearchStopping.RestartLaw
open scoped ENNReal BigOperators Classical

def aeMarkAccesses {R : Type} : List (AEAccessStep R) → ℕ
  | [] => 0
  | .mark :: w => aeMarkAccesses w + 1
  | _ :: w => aeMarkAccesses w

def aeSourceOracleAccesses {R : Type} : List (AEAccessStep R) → ℕ
  | [] => 0
  | .initialize :: w => aeSourceOracleAccesses w + 1
  | .mark :: w => aeSourceOracleAccesses w + 1
  | _ :: w => aeSourceOracleAccesses w

noncomputable def aeSourceEvaluations {I : Type} (M : ℕ) : ℕ :=
  aeSourceOracleAccesses (aeAccessWord (I := I) M)

def phaseAnchor (M : ℕ) (hM : 0 < M) : Fin M × (Bool × Fin M) :=
  ⟨⟨M - 1, by omega⟩, (false, ⟨M - 1, by omega⟩)⟩

noncomputable def restartSuccessMass (θ : ℝ) (j : ℕ) : ℝ :=
  (Real.sin ((2 * (j : ℝ) + 1) * θ)) ^ 2

noncomputable def restartProfile (θ : ℝ) (j : ℝ) : ℝ :=
  restartExpectedIterations θ j

noncomputable def restartWindow (M : ℕ) : Finset ℕ := Finset.Icc 1 M

noncomputable def restartWindowProfile (θ : ℝ) (M : ℕ) : Finset ℝ :=
  (restartWindow M).image (fun j : ℕ => restartProfile θ (j : ℝ))

noncomputable def restartOptimalValue (θ : ℝ) (M : ℕ) : ℝ :=
  if h : 0 < M then
    (restartWindowProfile θ M).min'
      (Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
  else 0

theorem restartIntegerOptimum_exists (θ : ℝ) (M : ℕ) (h : 0 < M) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ restartProfile θ (j : ℝ) = restartOptimalValue θ M := by
  have hne : (restartWindowProfile θ M).Nonempty :=
    Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  have hj' := Finset.mem_Icc.mp hj
  refine ⟨j, hj'.1, hj'.2, ?_⟩
  rw [restartOptimalValue, dif_pos h]
  exact heq

noncomputable def restartIntegerOptimum (θ : ℝ) (M : ℕ) : ℕ :=
  if h : 0 < M then Nat.find (restartIntegerOptimum_exists θ M h) else 0

noncomputable def restartRoundedDepth (θ z : ℝ) : ℕ :=
  Nat.floor (z / (4 * θ) + 1 / 2)

def aeWindow (M : ℕ) (k : ℕ) (a : ℝ) (z : Fin M) : Prop :=
  |aeEstimate M z - a| ≤
    2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (M : ℝ) +
      (k : ℝ) ^ 2 * Real.pi ^ 2 / (M : ℝ) ^ 2

def countWindow (N M : ℕ) (k : ℕ) (t : ℕ) (z : Fin M) : Prop :=
  |(N : ℝ) * aeEstimate M z - (t : ℝ)| ≤
    2 * Real.pi * (k : ℝ) * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ) +
      Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M : ℝ) ^ 2

noncomputable def countRounded (x : ℝ) : ℕ := Nat.floor (x + 1 / 2)

noncomputable def countGridSize (N : ℕ) : ℕ := Nat.ceil (Real.sqrt N)

noncomputable def countOutput (N M : ℕ) (z : Fin M) : ℕ :=
  countRounded ((N : ℝ) * aeEstimate M z)

def countAnchor (N : ℕ) (hN : 0 < N) : Fin N := ⟨0 % N, Nat.mod_lt _ hN⟩

noncomputable def countOutputWindow (N : ℕ) (t : ℕ) (M : ℕ) (z : Fin M) : Prop :=
  |(countOutput N M z : ℝ) - (t : ℝ)| <
    2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) + 11

theorem restartOptimalAngle_exists :
    ∃ z : ℝ, Real.tan (z / 2) = z ∧
      (233112 : ℝ) / 100000 < z ∧ z < (233113 : ℝ) / 100000 := by
  have h : ∃! z : ℝ, Real.tan (z / 2) = z ∧
      (233112 : ℝ) / 100000 < z ∧ z < (233113 : ℝ) / 100000 := section3OptimalAngleSubgoal
  exact h.exists

noncomputable def restartOptimalAngle : ℝ := Classical.choose restartOptimalAngle_exists

theorem restartOptimalAngle_spec :
    Real.tan (restartOptimalAngle / 2) = restartOptimalAngle ∧
      (233112 : ℝ) / 100000 < restartOptimalAngle ∧
      restartOptimalAngle < (233113 : ℝ) / 100000 :=
  Classical.choose_spec restartOptimalAngle_exists

noncomputable def restartScaledOptimum : ℝ := restartOptimalAngle / 4

noncomputable def restartScaledExpectation : ℝ :=
  restartOptimalAngle / (4 * Real.sin (restartOptimalAngle / 2) ^ 2)

noncomputable def restartStationarityResidual (x : ℝ) : ℝ := Real.tan x - 2 * x

noncomputable def restartScaledProfile (u : ℝ) : ℝ := u / Real.sin (2 * u) ^ 2

noncomputable def restartScaledProfileθ (u θ : ℝ) : ℝ := u / Real.sin (2 * u + θ) ^ 2

noncomputable def restartWindowDepth (θ : ℝ) : ℕ := Nat.floor (Real.pi / (4 * θ))

noncomputable def restartScaledSlack : ℝ := (Real.pi / 4) / Real.sin (1 / 8) ^ 4

noncomputable def restartScaledFloor : ℝ := 1 / 16

noncomputable def restartSourceEvaluations (j : ℕ) : ℕ := j + 2

noncomputable def restartSourceScale (N t : ℕ) : ℝ := Real.sqrt ((N : ℝ) / (t : ℝ))

noncomputable def bbhtCountPeriod (P : ℕ) (θ : ℝ) : ℝ := (P : ℝ) * θ / Real.pi

noncomputable def bbhtCountAngle (P : ℕ) (fObs : ℕ) : ℝ := (fObs : ℝ) * Real.pi / (P : ℝ)

noncomputable def bbhtCountEstimate (N P : ℕ) (fObs : ℕ) : ℝ :=
  (N : ℝ) * Real.sin (bbhtCountAngle P fObs) ^ 2

def bbhtCountHypothesis (P : ℕ) (θ : ℝ) (fObs : ℕ) : Prop :=
  |bbhtCountPeriod P θ - (fObs : ℝ)| < 1

noncomputable def bbhtCountWindow (N P t : ℝ) : ℝ :=
  2 * Real.pi / P * Real.sqrt (t * N) + Real.pi ^ 2 / P ^ 2 * N

noncomputable def bbhtCountGridSingle (N c : ℝ) : ℝ := c * Real.sqrt N

noncomputable def bbhtCountGridRelative (N t c : ℝ) : ℝ := c * Real.sqrt (N / t)

noncomputable def bbhtCountGridTwoStage (N t c : ℝ) : ℝ := c * Real.sqrt (t * N)

noncomputable def bbhtCountExactConstant : ℝ := 14

noncomputable def bbhtStageOneGrid (N c : ℝ) : ℝ := c * Real.sqrt N

noncomputable def bbhtStageTwoGrid (N t c : ℝ) : ℝ := c * Real.sqrt (t * N)

noncomputable def bbhtTwoStageTime (N t c : ℝ) : ℝ :=
  bbhtStageOneGrid N c + bbhtStageTwoGrid N t c

def bbhtPerfectSquare (t : ℕ) : Prop := ∃ m : ℕ, m * m = t

def bbhtOverStrongPerfectSquare (K : ℝ) : Prop :=
  ∀ (N : ℕ) (m : ℕ), 0 < N → 0 < m →
    bbhtTwoStageTime (N : ℝ) ((m * m : ℕ) : ℝ) bbhtCountExactConstant ≤ K * Real.sqrt N

structure NativeResourceLedger where

  queries : ℕ

  gates : ℕ

  fairBits : ℕ
  deriving DecidableEq, Repr

noncomputable def aeNativeLedger (M : ℕ) (A : Matrix (Fin M × (Bool × Fin M))
    (Fin M × (Bool × Fin M)) ℂ) (j : Fin M × (Bool × Fin M)) : NativeResourceLedger where
  queries := QueryCount (countedAECircuit (I := Fin M × (Bool × Fin M)) M A j)
  gates := GateCount (countedAECircuit (I := Fin M × (Bool × Fin M)) M A j)
  fairBits := 0

noncomputable def aePaddedAECircuit {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) : Circuit (Fin M × (Bool × I)) :=
  (countedAECircuit (I := I) M A j) ++ [Step.query]

noncomputable def aePaddedNativeLedger {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) : NativeResourceLedger where
  queries := QueryCount (aePaddedAECircuit (I := I) M A j)
  gates := GateCount (aePaddedAECircuit (I := I) M A j)
  fairBits := 0

noncomputable def exactCountRoughGrid (N : ℕ) : ℕ := BHMTTh17.exactCountM₀ N

noncomputable def exactCountFinalGrid (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  BHMTTh17.exactCountGrid N t'₁ t'₂

noncomputable def exactCountSourceEvaluations (M₀ M : ℕ) : ℕ := 2 * M₀ + M

def stateBits (x : ℕ) : ℕ := Nat.log 2 x + 1

def exactCountSpaceBits (N M : ℕ) : ℕ :=
  stateBits M + 3 * stateBits (N + 1)

noncomputable def exactCountFinalSuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (M : ℕ) (hM : 2 ≤ M) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin M => countOutput N M y = S.card),
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM).prob y

noncomputable def exactCountProcedureSuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountRoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (exactCountRoughGrid N),
      2 ≤ exactCountFinalGrid N
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₂)) : ℝ :=
  ∑ z₁ : Fin (exactCountRoughGrid N), ∑ z₂ : Fin (exactCountRoughGrid N),
    (aeLaw (exactCountRoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₁ *
    (aeLaw (exactCountRoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₂ *
    exactCountFinalSuccessMass hN S
      (exactCountFinalGrid N
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₂))
      (hM z₁ z₂)

noncomputable def exactCountProcedureCostMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountRoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (exactCountRoughGrid N),
      2 ≤ exactCountFinalGrid N
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₂)) : ℝ :=
  ∑ z₁ : Fin (exactCountRoughGrid N), ∑ z₂ : Fin (exactCountRoughGrid N),
    (aeLaw (exactCountRoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₁ *
    (aeLaw (exactCountRoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₂ *
    ((exactCountSourceEvaluations (exactCountRoughGrid N)
      (exactCountFinalGrid N
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (exactCountRoughGrid N) z₂)) : ℝ))

noncomputable def basicApproxCountRecordEvaluations (N M : ℕ) : ℕ :=
  aeSourceEvaluations (I := Fin N) M

noncomputable def basicApproxCountNativeCost (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : ℕ :=
  (∑ l : Fin (basicApproxCountLoopCap N),
    if l.val < basicApproxCountStop N ω then
      basicApproxCountRecordEvaluations N (2 * 2 ^ l.val) else 0) +
    basicApproxCountRecordEvaluations N
      (basicApproxCountFinalM ε (basicApproxCountStop N ω))

noncomputable def basicApproxCountProcedureCostMass {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N)) (ε : ℝ) : ℝ :=
  ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
    basicApproxCountPrefixWeight hN S ω *
      ((basicApproxCountNativeCost N ε ω : ℕ) : ℝ)

noncomputable def basicApproxCountRealFinalGrid (ε : ℝ) (s : ℕ) : ℝ :=
  20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ)

noncomputable def basicApproxCountSpaceBits (N M : ℕ) : ℕ :=
  stateBits M + stateBits (N + 1) + stateBits (basicApproxCountLoopCap N + 1)

def heuristicDescriptionBits (n : ℕ) : ℕ := n

def heuristicTrialCost (n : ℕ) (kappa : ℝ) : ℝ :=
  kappa * (heuristicDescriptionBits n : ℝ) + 1

noncomputable def heuristicQuantumAaCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ) : ℝ≥0∞ :=
  ∑ f : (Fin n → Bool), (D f) *
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
        (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
      (fun out => (out.2.1 : ℝ≥0∞))

noncomputable def heuristicQuantumFullCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ)
    (kappa : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (heuristicTrialCost n kappa) *
      BHMTTh6.heuristicQuantumChiCost hn G D T +
    heuristicQuantumAaCost hn G D T

noncomputable def heuristicClassicalFullCost (n : ℕ)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool))
    (kappa : ℝ) : ℝ :=
  heuristicTrialCost n kappa * BHMTTh6.heuristicClassicalTime n G D

noncomputable def approxCountL1 (s : ℕ) : ℕ :=
  Nat.ceil (9 * Real.pi * (2 ^ s : ℝ))

noncomputable def approxCountNegGrid (ε : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (168 * Real.pi / ε))

noncomputable def approxCountL2 (N ε : ℝ) (r₁ r₂ : ℝ) : ℕ :=
  Nat.ceil (2 * min (Real.sqrt (r₁ / (ε * N))) (Real.sqrt (r₂ / (ε * N)))) + 1

noncomputable def approxCountM1 (ε : ℝ) (L1 L2 : ℕ) : ℕ :=
  Nat.ceil ((1 / Real.sqrt ε) * (L1 : ℝ) * (1 + (L2 : ℝ)))

noncomputable def approxCountM2 (N : ℕ) (t' : ℝ) : ℕ :=
  Nat.ceil (30 * Real.sqrt ((t' + 1) * ((N : ℝ) - t' + 1)))

noncomputable def approxCountFinalM (M : ℕ) : ℕ :=
  Nat.ceil (10 * Real.pi * (M : ℝ))

noncomputable def approxCountOutput (N : ℕ) {M : ℕ} (z : Fin M) : ℤ :=
  ⌊(N : ℝ) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z + 1/2⌋

noncomputable def approxCountEffPrec (t : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor (ε * (t : ℝ)) + 1

noncomputable def approxCountSourceScale (N t : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt ((N : ℝ) / (approxCountEffPrec t ε : ℝ)) +
    Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (approxCountEffPrec t ε : ℝ)

noncomputable def approxCountScaleFirst (N t : ℕ) (ε : ℝ) : ℝ :=
  (1 / Real.sqrt ε) * Real.sqrt ((N : ℝ) / ((t : ℝ) + 1)) *
    (1 + Real.sqrt (((N : ℝ) - (t : ℝ)) / (ε * (N : ℝ))))

noncomputable def approxCountScaleSecond (N t : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt (((t : ℝ) + 1) * ((N : ℝ) - (t : ℝ) + 1))

noncomputable def approxCountSourceScalePrime (N t : ℕ) (ε : ℝ) : ℝ :=
  min (approxCountScaleFirst N t ε) (approxCountScaleSecond N t ε)

def approxCountSourceEpsilonRange (N : ℕ) (ε : ℝ) : Prop :=
  1 / (3 * (N : ℝ)) < ε ∧ ε ≤ 1

noncomputable def approxCountScaleEventProb : ℝ := (19 / 20 : ℝ) ^ 3

noncomputable def approxCountScaleEventFloor : ℝ := 17 / 20

noncomputable def approxCountFinalRecordProb : ℝ := 8 / Real.pi ^ 2

open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib

noncomputable def growthRejectProb (m : ℕ) : ℝ := thresholdRejectProb m

noncomputable def growthWidth (m : ℕ) : ℕ := thresholdWidth m

noncomputable def growthSamplerLaw (m r : ℕ) : PMF (ThresholdOutcome m r) :=
  thresholdRunLaw m r

def growthDraws {m r : ℕ} (o : ThresholdOutcome m r) : ℕ :=
  match o with
  | .accepted _ n => n.val + 1
  | .failed => r

noncomputable def growthBits {m r : ℕ} (o : ThresholdOutcome m r) : ℕ :=
  growthWidth m * growthDraws o

noncomputable def growthSpace (m : ℕ) : ℕ := growthWidth m

noncomputable def growthMarginal (m r : ℕ) (j : Fin m) : ℝ :=
  ∑ n : Fin r,
    ((growthSamplerLaw m r)
      (ThresholdOutcome.accepted j n : ThresholdOutcome m r)).toReal

noncomputable def growthMarginalAt (m r j : ℕ) : ℝ :=
  if hj : j < m then growthMarginal m r ⟨j, hj⟩ else 0

noncomputable def growthCheckedQueries (I : Type*) [Fintype I] [DecidableEq I]
    (j : ℕ) : ℝ :=
  ((QueryCount (LiftCircuit (SearchCircuit I j)) +
    QueryCount ([Step.query] : Circuit (I × Bool)) : ℕ) : ℝ)

noncomputable def growthRealWindow (N k : ℕ) : ℝ :=
  min ((6 / 5 : ℝ) ^ k) (Real.sqrt N)

noncomputable def nativeGrowthWindow (N k : ℕ) : ℕ :=
  Nat.ceil (min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ))

noncomputable def growthAttemptSuccess {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * (∑ i, CheckedOutputMass A j i)

noncomputable def growthAttemptQueries (I : Type*) [Fintype I] [DecidableEq I]
    (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * growthCheckedQueries I j

noncomputable def growthAttemptFailure {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * CheckedRejectMass A j

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification

def promiseGoodLabel {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool :=
  markLabels N S ((i : Fin N).val : ℤ)

theorem promiseGoodLabel_iff {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    promiseGoodLabel S i = true ↔ i ∈ S := by
  simp only [promiseGoodLabel, markLabels, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp h
    have hjq : j = i := Fin.val_inj.mp (by exact_mod_cast hval)
    rwa [hjq] at hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

noncomputable def promiseMarkedSpace {N : ℕ} (S : Finset (Fin N)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
  (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
    {i : Fin N | markLabels N S ((fun i : Fin N => (i.val : ℤ)) i) = true})).topologicalClosure

noncomputable def promiseGoodProjection {N : ℕ} (S : Finset (Fin N)) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ)) (markLabels N S)

noncomputable def promiseReadoutMass {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) (i : Fin N) : ℝ :=
  ‖v.1 i‖^2 + ‖v.2 i‖^2

noncomputable def promiseReadoutTotal {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) : ℝ :=
  ∑ i, promiseReadoutMass v i

def promiseDecision {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool :=
  decide (i ∈ S)

noncomputable def promiseFinalState {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (design : ℝ → ℝ × List (Fin 6)) (t₀ : ℕ) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  let d := design ((t₀ : ℝ)/(N : ℝ))
  promiseRun hN S d.1 d.2

noncomputable def promiseOutputWidth (N : ℕ) : ℕ := thresholdWidth N

noncomputable def promiseOutputWord {N : ℕ} (hN : 0 < N) (i : Fin N) :
    Fin (thresholdWords N) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (thresholdWords_ge N hN)⟩

noncomputable def promiseOutputDecode {N : ℕ} (hN : 0 < N) (w : Fin (thresholdWords N)) :
    Fin N :=
  if hw : w.val < N then ⟨w.val, hw⟩ else ⟨0, hN⟩

noncomputable def sourcePrintedTimeout (N : ℕ) : ℝ :=
  (45 / 2 : ℝ) * Real.sqrt (N : ℝ) + (7 / 5 : ℝ) * (binaryLog N) ^ 2

noncomputable def sourceNativeCutoff (N : ℕ) : ℕ := Nat.ceil (sourcePrintedTimeout N)

noncomputable def sourceNativeBudget (N : ℕ) : ℕ := sourceNativeCutoff N + N

noncomputable def sourceNativeClock (N : ℕ) (xs : List (SearchTrace N)) : ℝ :=
  (xs.map (fun x =>
    (Qatlib.Concepts.AmplitudeSearch.InterruptMin.TerminalCost
      (Qatlib.Concepts.SearchStopping.UnknownCount.ExponentialSizes N) x : ℝ) +
      (initCharge N : ℝ))).sum

noncomputable abbrev clause40SourceLaw {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) : RankedCallLaw N (SearchTrace N) :=
  sourceBBHTLaw ranked.indexOfRank hN

noncomputable abbrev clause40SourceSkip {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) : RankSkip N := ranked.skip

noncomputable def clause40AttainmentMassOn {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (cutoff : ℝ) : ℝ :=
  ∑' x : Fin N × List (SearchTrace N),
    if (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff then
      (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x else 0

noncomputable def clause40AttainmentMass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (cutoff : ℝ) : ℝ :=
  clause40AttainmentMassOn (SortedRankedTable.ofTable T) hN cutoff

noncomputable def clause41SingleSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (fun x => ∀ j, T x.1 ≤ T j)

noncomputable def clause41SingleFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (fun x => ¬∀ j, T x.1 ≤ T j)

noncomputable def clause41Placeholder {N : ℕ} (hN : 0 < N) : Fin N := ⟨(0 : ℕ), hN⟩

noncomputable def clause41IndependentPMF {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (clause41Placeholder hN, 0)
  | c' + 1 => (clause41IndependentPMF T hN budget c').bind fun p =>
      (chargedInitialPMF T hN budget).bind fun f =>
        PMF.pure (amplifiedCombine T p.1 f.1, p.2 + f.2)

noncomputable def clause41IndependentSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (clause41IndependentPMF T hN budget c) (fun x => ∀ j, T x.1 ≤ T j)

noncomputable def clause41IndependentFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (clause41IndependentPMF T hN budget c) (fun x => ¬∀ j, T x.1 ≤ T j)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
