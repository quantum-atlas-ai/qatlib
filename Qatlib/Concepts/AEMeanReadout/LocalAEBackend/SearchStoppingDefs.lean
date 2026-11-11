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

/-!
# Definitions for counting and search stopping consumers

This module defines access counts, numerical error windows, and resource ledgers used to connect
amplitude estimation to counting and search. The counting constructions include the procedures
studied in [BrassardEtAl2002], together with restart profiles and counting scales related to
[BoyerEtAl1998].

The remaining definitions describe bounded rejection sampling, marked-subspace readout, and
minimum-finding cutoff and repetition laws. In particular, `clause41IndependentPMF` retains an
initial candidate when combining independent runs, and `clause40AttainmentMass` measures the
source-clock cutoff event for the minimum-finding construction of [DurrHoyer1996].

## Main definitions

* `aeSourceOracleAccesses`: source accesses including initialization and marking.
* `aeWindow` and `countWindow`: amplitude and counting error predicates.
* `restartIntegerOptimum`: a minimizing integer restart depth in a finite window.
* `NativeResourceLedger`: query, gate, and fair-bit counts.
* `growthSamplerLaw`: a bounded rejection sampler for search depths.
* `clause41IndependentPMF`: independent minimum-finding runs combined with an initial candidate.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Boyer et al., 1998][BoyerEtAl1998]
* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

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

/-- The number of marking steps in an amplitude estimation access word. -/
def aeMarkAccesses {R : Type} : List (AEAccessStep R) → ℕ
  | [] => 0
  | .mark :: w => aeMarkAccesses w + 1
  | _ :: w => aeMarkAccesses w

/-- The number of initialization and marking steps in an amplitude estimation access word. -/
def aeSourceOracleAccesses {R : Type} : List (AEAccessStep R) → ℕ
  | [] => 0
  | .initialize :: w => aeSourceOracleAccesses w + 1
  | .mark :: w => aeSourceOracleAccesses w + 1
  | _ :: w => aeSourceOracleAccesses w

/-- The source oracle access count of the amplitude estimation access word for grid size `M`. -/
noncomputable def aeSourceEvaluations {I : Type} (M : ℕ) : ℕ :=
  aeSourceOracleAccesses (aeAccessWord (I := I) M)

/-- The phase-register anchor with both finite indices equal to `M - 1` and Boolean component
`false`. -/
def phaseAnchor (M : ℕ) (hM : 0 < M) : Fin M × (Bool × Fin M) :=
  ⟨⟨M - 1, by omega⟩, (false, ⟨M - 1, by omega⟩)⟩

/-- The success mass `sin ((2 * j + 1) * θ)²` after `j` amplification iterations. -/
noncomputable def restartSuccessMass (θ : ℝ) (j : ℕ) : ℝ :=
  (Real.sin ((2 * (j : ℝ) + 1) * θ)) ^ 2

/-- The real-valued restart expected-iteration profile at angle `θ` and depth `j`. -/
noncomputable def restartProfile (θ : ℝ) (j : ℝ) : ℝ :=
  restartExpectedIterations θ j

/-- The finite set of integer restart depths from one through `M`. -/
noncomputable def restartWindow (M : ℕ) : Finset ℕ := Finset.Icc 1 M

/-- The set of restart profile values at integer depths in `restartWindow M`. -/
noncomputable def restartWindowProfile (θ : ℝ) (M : ℕ) : Finset ℝ :=
  (restartWindow M).image (fun j : ℕ => restartProfile θ (j : ℝ))

/-- The minimum restart profile value on a positive finite window, with value zero when `M = 0`. -/
noncomputable def restartOptimalValue (θ : ℝ) (M : ℕ) : ℝ :=
  if h : 0 < M then
    (restartWindowProfile θ M).min'
      (Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
  else 0

/-- A positive finite restart window contains an integer depth attaining `restartOptimalValue θ
M`. -/
theorem restartIntegerOptimum_exists (θ : ℝ) (M : ℕ) (h : 0 < M) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ restartProfile θ (j : ℝ) = restartOptimalValue θ M := by
  have hne : (restartWindowProfile θ M).Nonempty :=
    Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  have hj' := Finset.mem_Icc.mp hj
  refine ⟨j, hj'.1, hj'.2, ?_⟩
  rw [restartOptimalValue, dif_pos h]
  exact heq

/-- The least integer depth attaining the minimum in a positive restart window, with value zero
for an empty window. -/
noncomputable def restartIntegerOptimum (θ : ℝ) (M : ℕ) : ℕ :=
  if h : 0 < M then Nat.find (restartIntegerOptimum_exists θ M h) else 0

/-- The natural-number rounding of `z / (4 * θ)`, defined by taking the natural floor after
adding one half. -/
noncomputable def restartRoundedDepth (θ z : ℝ) : ℕ :=
  Nat.floor (z / (4 * θ) + 1 / 2)

/-- The amplitude estimation error predicate with radius `2πk√(a(1 - a))/M + k²π²/M²`. -/
def aeWindow (M : ℕ) (k : ℕ) (a : ℝ) (z : Fin M) : Prop :=
  |aeEstimate M z - a| ≤
    2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (M : ℝ) +
      (k : ℝ) ^ 2 * Real.pi ^ 2 / (M : ℝ) ^ 2

/-- The unrounded counting error predicate with radius `2πk√(t(N - t))/M + π²k²N/M²`. -/
def countWindow (N M : ℕ) (k : ℕ) (t : ℕ) (z : Fin M) : Prop :=
  |(N : ℝ) * aeEstimate M z - (t : ℝ)| ≤
    2 * Real.pi * (k : ℝ) * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ) +
      Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M : ℝ) ^ 2

/-- Rounding to a natural number by taking the natural floor after adding one half. -/
noncomputable def countRounded (x : ℝ) : ℕ := Nat.floor (x + 1 / 2)

/-- The natural ceiling of `√N`, used as the counting grid size. -/
noncomputable def countGridSize (N : ℕ) : ℕ := Nat.ceil (Real.sqrt N)

/-- The natural-number rounding of `N` times the amplitude estimate at label `z`. -/
noncomputable def countOutput (N M : ℕ) (z : Fin M) : ℕ :=
  countRounded ((N : ℝ) * aeEstimate M z)

/-- The distinguished index with value `0 % N` in `Fin N` for positive `N`. -/
def countAnchor (N : ℕ) (hN : 0 < N) : Fin N := ⟨0 % N, Nat.mod_lt _ hN⟩

/-- The strict rounded-output error predicate with radius `2π√(t(N - t)/N) + 11`. -/
noncomputable def countOutputWindow (N : ℕ) (t : ℕ) (M : ℕ) (z : Fin M) : Prop :=
  |(countOutput N M z : ℝ) - (t : ℝ)| <
    2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) + 11

/-- There exists a solution of `tan (z / 2) = z` strictly between `2.33112` and `2.33113`. -/
theorem restartOptimalAngle_exists :
    ∃ z : ℝ, Real.tan (z / 2) = z ∧
      (233112 : ℝ) / 100000 < z ∧ z < (233113 : ℝ) / 100000 := by
  have h : ∃! z : ℝ, Real.tan (z / 2) = z ∧
      (233112 : ℝ) / 100000 < z ∧ z < (233113 : ℝ) / 100000 := section3OptimalAngleSubgoal
  exact h.exists

/-- A selected solution of the restart stationarity equation in the interval `(2.33112,
2.33113)`. -/
noncomputable def restartOptimalAngle : ℝ := Classical.choose restartOptimalAngle_exists

/-- The selected restart angle satisfies `tan (z / 2) = z` and the defining rational interval
bounds. -/
theorem restartOptimalAngle_spec :
    Real.tan (restartOptimalAngle / 2) = restartOptimalAngle ∧
      (233112 : ℝ) / 100000 < restartOptimalAngle ∧
      restartOptimalAngle < (233113 : ℝ) / 100000 :=
  Classical.choose_spec restartOptimalAngle_exists

/-- The optimal restart angle divided by four. -/
noncomputable def restartScaledOptimum : ℝ := restartOptimalAngle / 4

/-- The constant `z / (4 * sin (z / 2)²)` evaluated at the selected optimal restart angle. -/
noncomputable def restartScaledExpectation : ℝ :=
  restartOptimalAngle / (4 * Real.sin (restartOptimalAngle / 2) ^ 2)

/-- The stationarity residual `tan x - 2 * x` for the limiting restart profile. -/
noncomputable def restartStationarityResidual (x : ℝ) : ℝ := Real.tan x - 2 * x

/-- The limiting scaled restart profile `u / sin (2 * u)²`. -/
noncomputable def restartScaledProfile (u : ℝ) : ℝ := u / Real.sin (2 * u) ^ 2

/-- The shifted scaled restart profile `u / sin (2 * u + θ)²`. -/
noncomputable def restartScaledProfileθ (u θ : ℝ) : ℝ := u / Real.sin (2 * u + θ) ^ 2

/-- The natural floor of `π / (4 * θ)`, used to bound the integer restart window. -/
noncomputable def restartWindowDepth (θ : ℝ) : ℕ := Nat.floor (Real.pi / (4 * θ))

/-- The constant `(π / 4) / sin (1 / 8)⁴` used to compare shifted and limiting restart profiles. -/
noncomputable def restartScaledSlack : ℝ := (Real.pi / 4) / Real.sin (1 / 8) ^ 4

/-- The lower scaled-profile cutoff `1 / 16`. -/
noncomputable def restartScaledFloor : ℝ := 1 / 16

/-- The source evaluation cost `j + 2` at restart depth `j`. -/
noncomputable def restartSourceEvaluations (j : ℕ) : ℕ := j + 2

/-- The square-root source scale `√(N / t)`. -/
noncomputable def restartSourceScale (N t : ℕ) : ℝ := Real.sqrt ((N : ℝ) / (t : ℝ))

/-- The rescaled phase period `P * θ / π` in the counting readout. -/
noncomputable def bbhtCountPeriod (P : ℕ) (θ : ℝ) : ℝ := (P : ℝ) * θ / Real.pi

/-- The angle `fObs * π / P` reconstructed from a counting observation. -/
noncomputable def bbhtCountAngle (P : ℕ) (fObs : ℕ) : ℝ := (fObs : ℝ) * Real.pi / (P : ℝ)

/-- The count estimate `N * sin (fObs * π / P)²` reconstructed from the observed label. -/
noncomputable def bbhtCountEstimate (N P : ℕ) (fObs : ℕ) : ℝ :=
  (N : ℝ) * Real.sin (bbhtCountAngle P fObs) ^ 2

/-- The condition that the observed label differs from the rescaled phase period by less than
one. -/
def bbhtCountHypothesis (P : ℕ) (θ : ℝ) (fObs : ℕ) : Prop :=
  |bbhtCountPeriod P θ - (fObs : ℝ)| < 1

/-- The counting error radius `2π√(tN)/P + π²N/P²`. -/
noncomputable def bbhtCountWindow (N P t : ℝ) : ℝ :=
  2 * Real.pi / P * Real.sqrt (t * N) + Real.pi ^ 2 / P ^ 2 * N

/-- The single-stage counting grid scale `c * √N`. -/
noncomputable def bbhtCountGridSingle (N c : ℝ) : ℝ := c * Real.sqrt N

/-- The relative-error counting grid scale `c * √(N / t)`. -/
noncomputable def bbhtCountGridRelative (N t c : ℝ) : ℝ := c * Real.sqrt (N / t)

/-- The second-stage counting grid scale `c * √(tN)`. -/
noncomputable def bbhtCountGridTwoStage (N t c : ℝ) : ℝ := c * Real.sqrt (t * N)

/-- The constant `14` used in the exact-counting two-stage scale. -/
noncomputable def bbhtCountExactConstant : ℝ := 14

/-- The first-stage grid scale `c * √N`. -/
noncomputable def bbhtStageOneGrid (N c : ℝ) : ℝ := c * Real.sqrt N

/-- The second-stage grid scale `c * √(tN)`. -/
noncomputable def bbhtStageTwoGrid (N t c : ℝ) : ℝ := c * Real.sqrt (t * N)

/-- The sum of the first- and second-stage counting grid scales. -/
noncomputable def bbhtTwoStageTime (N t c : ℝ) : ℝ :=
  bbhtStageOneGrid N c + bbhtStageTwoGrid N t c

/-- The predicate that a natural number is the square of another natural number. -/
def bbhtPerfectSquare (t : ℕ) : Prop := ∃ m : ℕ, m * m = t

/-- The proposed uniform bound `K * √N` for two-stage counting time at every positive square
count. -/
def bbhtOverStrongPerfectSquare (K : ℝ) : Prop :=
  ∀ (N : ℕ) (m : ℕ), 0 < N → 0 < m →
    bbhtTwoStageTime (N : ℝ) ((m * m : ℕ) : ℝ) bbhtCountExactConstant ≤ K * Real.sqrt N

/-- A resource record containing natural-number query, gate, and fair-bit counts. -/
structure NativeResourceLedger where

  queries : ℕ

  gates : ℕ

  fairBits : ℕ
  deriving DecidableEq, Repr

/-- The query and gate counts of the counted amplitude estimation circuit, with zero fair-bit
cost. -/
noncomputable def aeNativeLedger (M : ℕ) (A : Matrix (Fin M × (Bool × Fin M))
    (Fin M × (Bool × Fin M)) ℂ) (j : Fin M × (Bool × Fin M)) : NativeResourceLedger where
  queries := QueryCount (countedAECircuit (I := Fin M × (Bool × Fin M)) M A j)
  gates := GateCount (countedAECircuit (I := Fin M × (Bool × Fin M)) M A j)
  fairBits := 0

/-- The counted amplitude estimation circuit followed by one additional query instruction. -/
noncomputable def aePaddedAECircuit {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) : Circuit (Fin M × (Bool × I)) :=
  (countedAECircuit (I := I) M A j) ++ [Step.query]

/-- The query and gate counts of the padded amplitude estimation circuit, with zero fair-bit
cost. -/
noncomputable def aePaddedNativeLedger {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) : NativeResourceLedger where
  queries := QueryCount (aePaddedAECircuit (I := I) M A j)
  gates := GateCount (aePaddedAECircuit (I := I) M A j)
  fairBits := 0

/-- The initial grid size used by the exact-counting procedure. -/
noncomputable def exactCountRoughGrid (N : ℕ) : ℕ := BHMTTh17.exactCountM₀ N

/-- The final exact-counting grid size selected from two real-valued rough estimates. -/
noncomputable def exactCountFinalGrid (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  BHMTTh17.exactCountGrid N t'₁ t'₂

/-- The source evaluation cost `2 * M₀ + M` for two rough records and one final record. -/
noncomputable def exactCountSourceEvaluations (M₀ M : ℕ) : ℕ := 2 * M₀ + M

/-- The bit-width expression `Nat.log 2 x + 1`. -/
def stateBits (x : ℕ) : ℕ := Nat.log 2 x + 1

/-- The space ledger consisting of one grid register and three registers of width `stateBits (N
+ 1)`. -/
def exactCountSpaceBits (N M : ℕ) : ℕ :=
  stateBits M + 3 * stateBits (N + 1)

/-- The probability that the final amplitude estimation record rounds to the exact marked-set
cardinality. -/
noncomputable def exactCountFinalSuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (M : ℕ) (hM : 2 ≤ M) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin M => countOutput N M y = S.card),
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM).prob y

/-- The exact-counting success mass averaged over two independent rough amplitude estimation
records. -/
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

/-- The source evaluation cost of exact counting averaged over two independent rough amplitude
estimation records. -/
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

/-- The source access cost of an amplitude estimation record with grid size `M` over `Fin N`. -/
noncomputable def basicApproxCountRecordEvaluations (N M : ℕ) : ℕ :=
  aeSourceEvaluations (I := Fin N) M

/-- The sum of source evaluation costs for loop records before the stopping index and the final
Basic Approx Count record. -/
noncomputable def basicApproxCountNativeCost (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : ℕ :=
  (∑ l : Fin (basicApproxCountLoopCap N),
    if l.val < basicApproxCountStop N ω then
      basicApproxCountRecordEvaluations N (2 * 2 ^ l.val) else 0) +
    basicApproxCountRecordEvaluations N
      (basicApproxCountFinalM ε (basicApproxCountStop N ω))

/-- The Basic Approx Count native source cost averaged over the product distribution of loop
records. -/
noncomputable def basicApproxCountProcedureCostMass {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N)) (ε : ℝ) : ℝ :=
  ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
    basicApproxCountPrefixWeight hN S ω *
      ((basicApproxCountNativeCost N ε ω : ℕ) : ℝ)

/-- The real-valued final grid scale `20 * π² * 2^s / ε` for Basic Approx Count. -/
noncomputable def basicApproxCountRealFinalGrid (ε : ℝ) (s : ℕ) : ℝ :=
  20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ)

/-- The register-width ledger for the grid, count, and loop index in Basic Approx Count. -/
noncomputable def basicApproxCountSpaceBits (N M : ℕ) : ℕ :=
  stateBits M + stateBits (N + 1) + stateBits (basicApproxCountLoopCap N + 1)

/-- The description-length cost assigned to a heuristic instance of size `n`. -/
def heuristicDescriptionBits (n : ℕ) : ℕ := n

/-- The full cost `kappa * n + 1` assigned to one heuristic trial. -/
def heuristicTrialCost (n : ℕ) (kappa : ℝ) : ℝ :=
  kappa * (heuristicDescriptionBits n : ℝ) + 1

/-- The expected amplitude amplification iteration cost of the bounded quantum heuristic search,
averaged over the input distribution. -/
noncomputable def heuristicQuantumAaCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ) : ℝ≥0∞ :=
  ∑ f : (Fin n → Bool), (D f) *
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
        (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
      (fun out => (out.2.1 : ℝ≥0∞))

/-- The quantum heuristic cost combining charged predicate calls with the expected amplification
iteration cost. -/
noncomputable def heuristicQuantumFullCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ)
    (kappa : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (heuristicTrialCost n kappa) *
      BHMTTh6.heuristicQuantumChiCost hn G D T +
    heuristicQuantumAaCost hn G D T

/-- The classical expected heuristic time multiplied by the full cost of one trial. -/
noncomputable def heuristicClassicalFullCost (n : ℕ)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool))
    (kappa : ℝ) : ℝ :=
  heuristicTrialCost n kappa * BHMTTh6.heuristicClassicalTime n G D

/-- The natural ceiling of `9 * π * 2^s` used in approximate counting. -/
noncomputable def approxCountL1 (s : ℕ) : ℕ :=
  Nat.ceil (9 * Real.pi * (2 ^ s : ℝ))

/-- The natural ceiling of `√(168 * π / ε)` used as a preliminary approximate-counting grid. -/
noncomputable def approxCountNegGrid (ε : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (168 * Real.pi / ε))

/-- One plus the ceiling of twice the smaller of the two rough-estimate precision scales. -/
noncomputable def approxCountL2 (N ε : ℝ) (r₁ r₂ : ℝ) : ℕ :=
  Nat.ceil (2 * min (Real.sqrt (r₁ / (ε * N))) (Real.sqrt (r₂ / (ε * N)))) + 1

/-- The natural ceiling of `L1 * (1 + L2) / √ε`, the first approximate-counting grid candidate. -/
noncomputable def approxCountM1 (ε : ℝ) (L1 L2 : ℕ) : ℕ :=
  Nat.ceil ((1 / Real.sqrt ε) * (L1 : ℝ) * (1 + (L2 : ℝ)))

/-- The natural ceiling of `30 * √((t' + 1) * (N - t' + 1))`, the second grid candidate. -/
noncomputable def approxCountM2 (N : ℕ) (t' : ℝ) : ℕ :=
  Nat.ceil (30 * Real.sqrt ((t' + 1) * ((N : ℝ) - t' + 1)))

/-- The final grid size obtained by taking the natural ceiling of `10 * π * M`. -/
noncomputable def approxCountFinalM (M : ℕ) : ℕ :=
  Nat.ceil (10 * Real.pi * (M : ℝ))

/-- The integer rounding of `N` times the amplitude estimate at label `z`. -/
noncomputable def approxCountOutput (N : ℕ) {M : ℕ} (z : Fin M) : ℤ :=
  ⌊(N : ℝ) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z + 1/2⌋

/-- The effective integer precision `Nat.floor (ε * t) + 1`. -/
noncomputable def approxCountEffPrec (t : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor (ε * (t : ℝ)) + 1

/-- The sum `√(N / p) + √(t(N - t)) / p`, where `p` is the effective integer precision. -/
noncomputable def approxCountSourceScale (N t : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt ((N : ℝ) / (approxCountEffPrec t ε : ℝ)) +
    Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (approxCountEffPrec t ε : ℝ)

/-- The first source scale `√(N / (t + 1)) * (1 + √((N - t)/(εN))) / √ε`. -/
noncomputable def approxCountScaleFirst (N t : ℕ) (ε : ℝ) : ℝ :=
  (1 / Real.sqrt ε) * Real.sqrt ((N : ℝ) / ((t : ℝ) + 1)) *
    (1 + Real.sqrt (((N : ℝ) - (t : ℝ)) / (ε * (N : ℝ))))

/-- The second source scale `√((t + 1) * (N - t + 1))`. -/
noncomputable def approxCountScaleSecond (N t : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt (((t : ℝ) + 1) * ((N : ℝ) - (t : ℝ) + 1))

/-- The smaller of the first and second approximate-counting source scales. -/
noncomputable def approxCountSourceScalePrime (N t : ℕ) (ε : ℝ) : ℝ :=
  min (approxCountScaleFirst N t ε) (approxCountScaleSecond N t ε)

/-- The source precision range `1 / (3 * N) < ε ≤ 1`. -/
def approxCountSourceEpsilonRange (N : ℕ) (ε : ℝ) : Prop :=
  1 / (3 * (N : ℝ)) < ε ∧ ε ≤ 1

/-- The scale-event probability constant `(19 / 20)³`. -/
noncomputable def approxCountScaleEventProb : ℝ := (19 / 20 : ℝ) ^ 3

/-- The lower comparison constant `17 / 20` for the scale-event probability. -/
noncomputable def approxCountScaleEventFloor : ℝ := 17 / 20

/-- The final-record success probability constant `8 / π²`. -/
noncomputable def approxCountFinalRecordProb : ℝ := 8 / Real.pi ^ 2

open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib

/-- The rejection probability of one threshold-sampling trial for a window of size `m`. -/
noncomputable def growthRejectProb (m : ℕ) : ℝ := thresholdRejectProb m

/-- The fair-bit word width used by the threshold sampler for a window of size `m`. -/
noncomputable def growthWidth (m : ℕ) : ℕ := thresholdWidth m

/-- The threshold-sampler law with window size `m` and at most `r` draws. -/
noncomputable def growthSamplerLaw (m r : ℕ) : PMF (ThresholdOutcome m r) :=
  thresholdRunLaw m r

/-- The number of threshold-sampler draws, equal to the accepted draw index plus one or to `r`
on failure. -/
def growthDraws {m r : ℕ} (o : ThresholdOutcome m r) : ℕ :=
  match o with
  | .accepted _ n => n.val + 1
  | .failed => r

/-- The threshold sampler's word width multiplied by its number of draws. -/
noncomputable def growthBits {m r : ℕ} (o : ThresholdOutcome m r) : ℕ :=
  growthWidth m * growthDraws o

/-- The working bit width of the threshold sampler. -/
noncomputable def growthSpace (m : ℕ) : ℕ := growthWidth m

/-- The total real probability of accepting a given depth, summed over all possible accepted
draw indices. -/
noncomputable def growthMarginal (m r : ℕ) (j : Fin m) : ℝ :=
  ∑ n : Fin r,
    ((growthSamplerLaw m r)
      (ThresholdOutcome.accepted j n : ThresholdOutcome m r)).toReal

/-- The acceptance marginal at a natural depth below `m`, extended by zero outside the window. -/
noncomputable def growthMarginalAt (m r j : ℕ) : ℝ :=
  if hj : j < m then growthMarginal m r ⟨j, hj⟩ else 0

/-- The query count of a lifted search circuit at depth `j` together with one checking query,
cast to a real number. -/
noncomputable def growthCheckedQueries (I : Type*) [Fintype I] [DecidableEq I]
    (j : ℕ) : ℝ :=
  ((QueryCount (LiftCircuit (SearchCircuit I j)) +
    QueryCount ([Step.query] : Circuit (I × Bool)) : ℕ) : ℝ)

/-- The real search window `min ((6 / 5)^k) (√N)`. -/
noncomputable def growthRealWindow (N k : ℕ) : ℝ :=
  min ((6 / 5 : ℝ) ^ k) (Real.sqrt N)

/-- The natural ceiling of the growth scale capped by the natural square root of `N`. -/
noncomputable def nativeGrowthWindow (N k : ℕ) : ℕ :=
  Nat.ceil (min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ))

/-- The marked-output mass of a checked search attempt, weighted by the bounded sampler's depth
marginals. -/
noncomputable def growthAttemptSuccess {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * (∑ i, CheckedOutputMass A j i)

/-- The checked search query cost weighted by the bounded sampler's accepted-depth marginals. -/
noncomputable def growthAttemptQueries (I : Type*) [Fintype I] [DecidableEq I]
    (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * growthCheckedQueries I j

/-- The rejection mass of a checked search attempt, weighted by the bounded sampler's depth
marginals. -/
noncomputable def growthAttemptFailure {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, growthMarginalAt m r j * CheckedRejectMass A j

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification

/-- The Boolean marked-label predicate on finite basis indices. -/
def promiseGoodLabel {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool :=
  markLabels N S ((i : Fin N).val : ℤ)

/-- A finite basis label is marked by `promiseGoodLabel` exactly when it belongs to `S`. -/
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

/-- The closed complex linear span of the standard basis vectors whose labels are marked. -/
noncomputable def promiseMarkedSpace {N : ℕ} (S : Finset (Fin N)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
  (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
    {i : Fin N | markLabels N S ((fun i : Fin N => (i.val : ℤ)) i) = true})).topologicalClosure

/-- The continuous complex-linear good-space projection determined by the standard basis and
marked labels. -/
noncomputable def promiseGoodProjection {N : ℕ} (S : Finset (Fin N)) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ)) (markLabels N S)

/-- The sum of squared coordinate norms from the two components of a paired output state at
label `i`. -/
noncomputable def promiseReadoutMass {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) (i : Fin N) : ℝ :=
  ‖v.1 i‖^2 + ‖v.2 i‖^2

/-- The total readout mass obtained by summing `promiseReadoutMass` over every finite label. -/
noncomputable def promiseReadoutTotal {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) : ℝ :=
  ∑ i, promiseReadoutMass v i

/-- The Boolean decision whether a finite output label belongs to the marked set. -/
def promiseDecision {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Bool :=
  decide (i ∈ S)

/-- The paired final state produced by the chosen design at promised success fraction `t₀ / N`. -/
noncomputable def promiseFinalState {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (design : ℝ → ℝ × List (Fin 6)) (t₀ : ℕ) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  let d := design ((t₀ : ℝ)/(N : ℝ))
  promiseRun hN S d.1 d.2

/-- The threshold word width used to encode an output label among `N` possibilities. -/
noncomputable def promiseOutputWidth (N : ℕ) : ℕ := thresholdWidth N

/-- The threshold word encoding a finite output label with the same natural value. -/
noncomputable def promiseOutputWord {N : ℕ} (hN : 0 < N) (i : Fin N) :
    Fin (thresholdWords N) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (thresholdWords_ge N hN)⟩

/-- Decoding a threshold word to its finite label when valid, with label zero as the fallback. -/
noncomputable def promiseOutputDecode {N : ℕ} (hN : 0 < N) (w : Fin (thresholdWords N)) :
    Fin N :=
  if hw : w.val < N then ⟨w.val, hw⟩ else ⟨0, hN⟩

/-- The real timeout `(45 / 2) * √N + (7 / 5) * (binaryLog N)²` used in the source
minimum-finding bound. -/
noncomputable def sourcePrintedTimeout (N : ℕ) : ℝ :=
  (45 / 2 : ℝ) * Real.sqrt (N : ℝ) + (7 / 5 : ℝ) * (binaryLog N) ^ 2

/-- The natural ceiling of the source's printed real timeout. -/
noncomputable def sourceNativeCutoff (N : ℕ) : ℕ := Nat.ceil (sourcePrintedTimeout N)

/-- The source native cutoff plus `N`, allowing an additional per-call budget. -/
noncomputable def sourceNativeBudget (N : ℕ) : ℕ := sourceNativeCutoff N + N

/-- The sum of terminal search costs and initialization charges over a list of minimum-finding
search traces. -/
noncomputable def sourceNativeClock (N : ℕ) (xs : List (SearchTrace N)) : ℝ :=
  (xs.map (fun x =>
    (Qatlib.Concepts.AmplitudeSearch.InterruptMin.TerminalCost
      (Qatlib.Concepts.SearchStopping.UnknownCount.ExponentialSizes N) x : ℝ) +
      (initCharge N : ℝ))).sum

/-- The source ranked-call law obtained from the sorted table's rank-to-index map. -/
noncomputable abbrev clause40SourceLaw {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) : RankedCallLaw N (SearchTrace N) :=
  sourceBBHTLaw ranked.indexOfRank hN

/-- The rank-skipping map induced by the sorted table. -/
noncomputable abbrev clause40SourceSkip {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) : RankSkip N := ranked.skip

/-- The total initial mass of source runs whose clock is at most the given cutoff for a sorted
ranked table. -/
noncomputable def clause40AttainmentMassOn {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (cutoff : ℝ) : ℝ :=
  ∑' x : Fin N × List (SearchTrace N),
    if (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff then
      (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x else 0

/-- The source-clock cutoff attainment mass after sorting the given table. -/
noncomputable def clause40AttainmentMass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (cutoff : ℝ) : ℝ :=
  clause40AttainmentMassOn (SortedRankedTable.ofTable T) hN cutoff

/-- The probability that one charged minimum-finding run returns a global minimizer within the
specified budget model. -/
noncomputable def clause41SingleSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (fun x => ∀ j, T x.1 ≤ T j)

/-- The probability that one charged minimum-finding run returns a label that is not a global
minimizer. -/
noncomputable def clause41SingleFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (fun x => ¬∀ j, T x.1 ≤ T j)

/-- The initial candidate at finite index zero for a nonempty table. -/
noncomputable def clause41Placeholder {N : ℕ} (hN : 0 < N) : Fin N := ⟨(0 : ℕ), hN⟩

/-- The law obtained by combining `c` independent charged runs with the initial candidate and
summing their costs. -/
noncomputable def clause41IndependentPMF {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (clause41Placeholder hN, 0)
  | c' + 1 => (clause41IndependentPMF T hN budget c').bind fun p =>
      (chargedInitialPMF T hN budget).bind fun f =>
        PMF.pure (amplifiedCombine T p.1 f.1, p.2 + f.2)

/-- The probability that the combined candidate from the independent-run law is a global
minimizer. -/
noncomputable def clause41IndependentSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (clause41IndependentPMF T hN budget c) (fun x => ∀ j, T x.1 ≤ T j)

/-- The probability that the combined candidate from the independent-run law is not a global
minimizer. -/
noncomputable def clause41IndependentFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (clause41IndependentPMF T hN budget c) (fun x => ¬∀ j, T x.1 ≤ T j)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
