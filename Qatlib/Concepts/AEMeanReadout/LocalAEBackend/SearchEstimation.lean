/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchEstimationDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ComparativeStrictBounds
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountingOracleTransport
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.EffectiveIntegerReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnknownSigmaMean

/-!
# Search and estimation endpoint guarantees

This module assembles source quantum-search semantics, termination, and expected ledger bounds
together with rational readout and strict amplitude-estimation success bounds. The search and
counting results follow the framework of [BrassardEtAl2002], with the exact boundary correction
between source and shifted search windows retained.

The endpoint theorems also collect integer readout properties, oracle-cost transport, and
confidence and access bounds for mean estimation with an unknown variance, in the setting of
[Montanaro2015].

## Main statements

* `clause78_endpoint` and `clause79_endpoint`: source search costs, survival, and stopping
  properties.
* `clause83_endpoint`: strict phase-window, amplitude-estimation, and counting probability
  bounds.
* `clause85_endpoint`: effective rational and integer readout guarantees.
* `clause8_endpoint`: unknown-variance mean-estimation confidence and resource bounds.
* `clause84_endpoint`: record and path oracle-cost transport identities.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.PilotVariance

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The source round succeeds with probability a + (1 − a) · w, where a is the initial marked
probability and w is the source-window average. -/
theorem s2_source_search_law (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (s2SourceRound A hA j₀ S l)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * sourceWindowAverage A j₀ S (qSearchWindow l) :=
  sourceRound_successMass A hA j₀ S l

/-- The source-minus-BHMT round success probability equals (1 − a) times the endpoint
depth-success difference divided by the search-window size, where a is the initial marked
probability. -/
theorem s2_source_search_exact_relation_to_frozen_shifted (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (s2SourceRound A hA j₀ S l)
      - roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l)
      = (1 - MeasureProb (preparedAAState A j₀) S)
        * ((depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
            / (qSearchWindow l : ℝ)) := by
  rw [← shiftedRound_eq_frozenRound A hA j₀ S l]
  exact sourceRound_successMass_sub_shiftedRound A hA j₀ S l

/-- The source and existing BHMT rounds have different success probabilities when the two
endpoint depth-success masses differ and the initial marked probability is not one. -/
theorem s2_source_search_ne_frozen_shifted_of_boundary (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ)
    (hbound : depthSuccessMass A j₀ S (qSearchWindow l) ≠ depthSuccessMass A j₀ S 0)
    (hA1 : MeasureProb (preparedAAState A j₀) S ≠ 1) :
    roundSuccessMass (s2SourceRound A hA j₀ S l)
      ≠ roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l) := by
  rw [← shiftedRound_eq_frozenRound A hA j₀ S l]
  exact sourceRound_successMass_ne_shiftedRound_of_boundary A hA j₀ S l hbound hA1

/-- The stage-two source round is definitionally the source quantum-search round. -/
theorem s2_source_step_is_s1_readout_round (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    s2SourceRound A hA j₀ S l = sourceQSearchRound A hA j₀ S l :=
  rfl

/-- The rational estimation readout is no greater than the ideal amplitude estimate and has
absolute error strictly less than 2^(−b). -/
theorem s2_estimation_readout_terminating (M : ℕ) (b : ℕ) (z : Fin M) :
    (s2EstimationReadout M b z : ℝ) ≤ aeEstimate M z ∧
      |(s2EstimationReadout M b z : ℝ) - aeEstimate M z| * (2 : ℝ)^b < 1 := by
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  constructor
  · exact dyadicRound_le b (aeEstimate M z)
  · exact dyadicRound_error b (aeEstimate M z)

/-- The estimation readout at the zero phase label is zero, and dyadic rounding fixes one. -/
theorem s2_estimation_readout_boundaries (M : ℕ) (b : ℕ) (hM : 0 < M) :
    s2EstimationReadout M b ⟨0, by omega⟩ = 0 ∧ dyadicRound b 1 = 1 :=
  ⟨by simp [s2EstimationReadout, labelReadout, aeEstimate, dyadicRound_zero],
    dyadicRound_one b⟩

/-- For positive initial marked probability, the source search survival probability tends to
zero as the number of steps tends to infinity. -/
theorem s2_unbounded_search_terminates (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Tendsto (sourceSurvival A hA j₀ S) atTop (𝓝 0) :=
  sourceSurvival_tendsto_zero A hA j₀ S ha

/-- When the initial marked probability is zero, the source search survival probability equals
one at every finite step. -/
theorem s2_unbounded_search_never_halts (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    ∀ n, sourceSurvival A hA j₀ S n = 1 :=
  sourceSurvival_eq_one_of_zero A hA j₀ S ha

/-- Every supported halting configuration of a source transition that returns an index returns
an element of the marked set. -/
theorem s2_unbounded_search_halts_marked (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r c1 c2 : ℕ) (cfg : Configuration SourceRunState (SourceRunOutcome I))
    (hcfg : cfg ∈ (sourceTransition A hA j₀ S r c1 c2).support) :
    ∀ y c1' c2', cfg = Sum.inl (some y, c1', c2') → y ∈ S :=
  sourceTransition_halt_marked A hA j₀ S r c1 c2 cfg hcfg

/-- For positive initial marked probability, the stopping distribution assigns each step its
specified `sourceStopMass`. -/
theorem s2_unbounded_search_stopping_law (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    ∀ k, sourceStopLaw A hA j₀ S ha k = sourceStopMass A hA j₀ S k :=
  sourceStopLaw_mass A hA j₀ S ha

/-- The source transition used here is the same fully qualified local-backend source transition. -/
theorem s2_unbounded_transition_is_s1_unbounded_transition (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r c1 c2 : ℕ) :
    sourceTransition A hA j₀ S r c1 c2
      = Qatlib.Concepts.AEMeanReadout.LocalAEBackend.sourceTransition A hA j₀ S r c1 c2 :=
  rfl

/-- The expected first ledger of a truncated source loop cannot decrease when its horizon
increases by one. -/
theorem s2_cumulative_ledger_expectation_mono (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S (T+1) 0)
          (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceLoop_ledger1_expectation_mono A hA j₀ S T

/-- The expected accumulated first ledger of N execution steps equals the expected first ledger
of the source loop truncated to N rounds. -/
theorem s2_unbounded_execution_matches_truncated_loop (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (N : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N (sourceInitial (I := I)))
        (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S N 0)
          (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceRunFor_ledger_eq_sourceLoop A hA j₀ S (fun c1 c2 => c1)
    (fun _ _ _ _ => rfl) (by rfl) N

/-- The expected first ledger of a finite source loop is the sum of the round expectations
weighted by their reach probabilities. -/
theorem s2_cumulative_ledger_expectation_unfold (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
            (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceQSearchLoop_ledger_expectation_unfold A hA j₀ S
    (fun out => (out.2.1 : ℝ≥0∞)) (fun _ out => by simp only []; rw [Nat.cast_add])
    (by simp) T

/-- Expected accumulated first-ledger costs of finite executions converge to the corresponding
infinite source-search cost series. -/
theorem s2_stop_cost_expectation_is_limit (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    Tendsto (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
        (sourceInitial (I := I)))
        (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞)))
      atTop (𝓝 (sourceStopLedgerExpectation A hA j₀ S
        (fun out => (out.2.1 : ℝ≥0∞)))) :=
  sourceStopLedgerExpectation_eq_limit A hA j₀ S (fun c1 c2 => c1)
    (fun _ _ _ _ => rfl) (by rfl)

/-- A mature source round has failure probability at most 3/4 under the stated amplitude-angle
and window hypotheses. -/
theorem s2_mature_source_round_fails_at_most_three_quarters (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) * Real.sin (2 * θ)) :
    1 - roundSuccessMass (sourceQSearchRound A hA j₀ S l) ≤ 3 / 4 :=
  sourceRound_fail_prob_le_three_quarters A hA j₀ S θ l hθ0 hθ1 hprob hmature

/-- Source round l has expected first ledger at most 6(6/5)^l and expected second ledger at most
4(6/5)^l. -/
theorem s2_source_round_ledger_cost (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) :=
  ⟨sourceRound_ledger1_expectation_le A hA j₀ S l,
    sourceRound_ledger2_expectation_le A hA j₀ S l⟩

/-- For positive initial marked probability a, both expected ledgers of every truncated source
loop are at most 400/√a. -/
theorem s2_source_search_two_ledger_budget (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
  ⟨sourceLoop_ledger1_expectation_le A hA j₀ S T ha,
    sourceLoop_ledger2_expectation_le A hA j₀ S T ha⟩

/-- For positive initial marked probability a, both infinite source-search ledger expectation
series retain the bound 400/√a. -/
theorem s2_unbounded_stop_cost_retains_sqrt_a_budget (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
  sourceStopLedgerExpectation_le A hA j₀ S ha

/-- For a positive grid M and real k > 1, the BHMT phase-window mass at radius k/M is strictly
greater than 1 − 1/(2(k − 1)) [BrassardEtAl2002]. -/
theorem s2_strict_bhmt_window_mass (M : ℕ) (ω : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k) :
    1 - 1 / (2 * (k - 1)) < bhmt11WindowMass M ω (k / (M : ℝ)) :=
  bhmt11WindowMass_strict M ω hM k hk

/-- For M ≥ 2 and natural k ≥ 2, the amplitude-estimation event with error at most 2πk√(a(1 −
a))/M + k²π²/M² has probability strictly greater than 1 − 1/(2(k − 1)) [BrassardEtAl2002]. -/
theorem s2_strict_ae_success_probability (M : ℕ) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (k : ℕ) (hk : 2 ≤ k) :
    let a := MeasureProb (preparedAAState A j) S
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) + (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)) :=
  preparedAeWindow_strict M A j S hM hA k hk

/-- For a nonempty universe, M ≥ 2, and k ≥ 2, quantum counting lies within the stated error
bound around the marked-set cardinality with probability strictly greater than 1 − 1/(2(k −
1)) [BrassardEtAl2002]. -/
theorem s2_strict_counting_success_probability (N M : ℕ) (S : Finset (Fin N))
    (hN : 0 < N) (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ) +
            Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
      (aeLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z >
        1 - 1 / (2 * ((k : ℝ) - 1)) :=
  countingWindow_strict N M S hN hM k hk

/-- Collects effective label precision, integer-count error and range bounds, upward
half-integer tie handling, rounding discontinuity, readout comparison, bit budgets, and the
integer-readout transport specification. -/
theorem clause85_endpoint :

    (∀ (M k : ℕ) (z : Fin M),
      0 ≤ effectiveLabelEstimate M k z ∧ effectiveLabelEstimate M k z ≤ 1 ∧
        |(effectiveLabelEstimate M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k) ∧

    ((1 : ℝ) / 2 ≤ 2 / 3) ∧
    (∀ (N M k : ℕ) (z : Fin M),
      |(effectiveIntegerCount N M k z : ℝ) - (N : ℝ) * aeEstimate M z| ≤
        (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2) ∧

    (∀ (N M k : ℕ) (z : Fin M),
      0 ≤ effectiveIntegerCount N M k z ∧ effectiveIntegerCount N M k z ≤ N) ∧

    (∀ (N M k : ℕ) (z : Fin M) (n : ℤ),
      (N : ℚ) * effectiveLabelEstimate M k z = (n : ℚ) + 1 / 2 →
      effectiveIntegerCount N M k z = n + 1) ∧

    (∀ (n : ℤ) (ε : ℝ), 0 < ε →
      ∃ x y : ℚ,
        |(x : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound x = n ∧
        |(y : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound y = n + 1) ∧

    (∀ (N M k : ℕ) (z : Fin M),
      |(effectiveIntegerCount N M k z : ℝ) - (countLabelReadoutNearest N M z : ℝ)| ≤
        effRoundSlack N k) ∧

    (∀ (N M k : ℕ) (z : Fin M),
      effectiveIntegerCount N M k z = aeEffCount N M k z) ∧

    (∀ N k : ℕ,
      Nat.clog 2 (N + 1) + k ≤ effCountBitBudget N k ∧
      2 * effCountBitBudget N k ≤ effCountSpaceBudget N k) ∧

    effectiveIntegerReadoutTransportsSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M k z
    exact ⟨(effectiveLabelEstimate_mem M k z).1, (effectiveLabelEstimate_mem M k z).2,
      effectiveLabelEstimate_error M k z⟩
  · norm_num
  · intro N M k z
    exact effectiveIntegerCount_error N M k z
  · intro N M k z
    exact effectiveIntegerCount_valid N M k z
  · intro N M k z n h
    exact effectiveIntegerCount_tie N M k z n h
  · intro n ε hε
    exact effectiveIntegerReadout_boundary_density n ε hε
  · intro N M k z
    exact effectiveIntegerCount_near_dev_nearest N M k z
  · intro N M k z
    exact effectiveIntegerCount_eq_frozen N M k z
  · intro N k
    exact effectiveIntegerReadout_budgets N k
  · exact effectiveIntegerReadout_transports

/-- Collects the source depth convention, round and loop ledger bounds, the exact
source-versus-shifted success correction, shared source and BHMT cost bounds, and survival
equal to one when the initial marked probability is zero [BrassardEtAl2002]. -/
theorem clause78_endpoint :

    (∀ (M : ℕ) (i : Fin M), sourceDepth M i = i.val + 1) ∧
    (∀ (l : ℕ) (i : Fin (qSearchWindow l)),
      sourceDepth (qSearchWindow l) i = i.val + 1) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (l : ℕ),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (T : ℕ),
      0 < MeasureProb (preparedAAState A j₀) S →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (l : ℕ),
      roundSuccessMass (sourceQSearchRound A hA j₀ S l)
        - roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l)
        = (1 - MeasureProb (preparedAAState A j₀) S)
          * ((depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
              / (qSearchWindow l : ℝ))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (T : ℕ),
      0 < MeasureProb (preparedAAState A j₀) S →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      MeasureProb (preparedAAState A j₀) S = 0 →
      ∀ n, sourceSurvival A hA j₀ S n = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M i
    rfl
  · intro l i
    rfl
  · intro A hA j₀ S l
    exact s2_source_round_ledger_cost A hA j₀ S l
  · intro A hA j₀ S T ha
    exact s2_source_search_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S l
    exact s2_source_search_exact_relation_to_frozen_shifted A hA j₀ S l
  · intro A hA j₀ S T ha
    exact source_and_shifted_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S ha n
    exact s2_unbounded_search_never_halts A hA j₀ S ha n

/-- Collects vanishing survival for positive initial marked probability, correctness of returned
marked indices, convergence of first-ledger execution expectations, both infinite ledger
bounds, and unit survival when the initial marked probability is zero. -/
theorem clause79_endpoint :

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      0 < MeasureProb (preparedAAState A j₀) S →
      Tendsto (sourceSurvival A hA j₀ S) atTop (𝓝 0)) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (r c1 c2 : ℕ) (cfg : Configuration SourceRunState (SourceRunOutcome I)),
      cfg ∈ (sourceTransition A hA j₀ S r c1 c2).support →
      ∀ y c1' c2', cfg = Sum.inl (some y, c1', c2') → y ∈ S) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      Tendsto (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
          (sourceInitial (I := I)))
          (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞)))
        atTop (𝓝 (sourceStopLedgerExpectation A hA j₀ S
          (fun out => (out.2.1 : ℝ≥0∞))))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      0 < MeasureProb (preparedAAState A j₀) S →
      sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      MeasureProb (preparedAAState A j₀) S = 0 →
      ∀ n, sourceSurvival A hA j₀ S n = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA j₀ S ha
    exact s2_unbounded_search_terminates A hA j₀ S ha
  · intro A hA j₀ S r c1 c2 cfg hcfg
    exact s2_unbounded_search_halts_marked A hA j₀ S r c1 c2 cfg hcfg
  · intro A hA j₀ S
    exact s2_stop_cost_expectation_is_limit A hA j₀ S
  · intro A hA j₀ S ha
    exact s2_unbounded_stop_cost_retains_sqrt_a_budget A hA j₀ S ha
  · intro A hA j₀ S ha n
    exact s2_unbounded_search_never_halts A hA j₀ S ha n

/-- Collects strict BHMT phase-window, amplitude-estimation, and counting success bounds,
together with their stated zero-amplitude, unit-amplitude, and odd-grid specializations
[BrassardEtAl2002]. -/
theorem clause83_endpoint :

    (∀ (M : ℕ) (ω : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k),
      1 - 1 / (2 * (k - 1)) < bhmt11WindowMass M ω (k / (M : ℝ))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      let a := MeasureProb (preparedAAState A j) S
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |aeEstimate M z - a| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) + (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
        (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1))) ∧

    (∀ (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k),
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ) +
              Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
        (aeLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z >
          1 - 1 / (2 * ((k : ℝ) - 1))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      MeasureProb (preparedAAState A j) S = 0 →
        (let a := MeasureProb (preparedAAState A j) S
         ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
             |aeEstimate M z - a| ≤
               2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) +
                 (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
           (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      MeasureProb (preparedAAState A j) S = 1 →
        (let a := MeasureProb (preparedAAState A j) S
         ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
             |aeEstimate M z - a| ≤
               2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) +
                 (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
           (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      M % 2 = 1 →
        (let a := MeasureProb (preparedAAState A j) S
         ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
             |aeEstimate M z - a| ≤
               2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) +
                 (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
           (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M ω hM k hk
    exact s2_strict_bhmt_window_mass M ω hM k hk
  · intro M A j S hM hA k hk
    exact s2_strict_ae_success_probability M A j S hM hA k hk
  · intro N M S hN hM k hk
    exact s2_strict_counting_success_probability N M S hN hM k hk
  · intro M A j S hM hA k hk ha
    exact s2_strict_ae_success_probability M A j S hM hA k hk
  · intro M A j S hM hA k hk ha
    exact s2_strict_ae_success_probability M A j S hM hA k hk
  · intro M A j S hM hA k hk hodd
    exact s2_strict_ae_success_probability M A j S hM hA k hk

/-- Under the stated bounded-payoff and pilot assumptions, the unknown-variance estimator has
failure mass at most (8/9)^r + 2/(Nν²). It also satisfies the displayed second- and
fourth-moment bounds, variance comparison, and pilot moment failure bound [Montanaro2015]. -/
theorem clause8_confidence_endpoint
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    (SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (unknownSigmaFails A j hA f nu eps N h K r hk)
      ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2)) ∧
    (unknownSigmaSecondMoment A j hA f ≤ 1 ∧ unknownSigmaFourthMoment A j hA f ≤ 1) ∧
    ((signedMeanSource A j hA).variance (fun i => (f i : ℝ))^2
      ≤ unknownSigmaFourthMoment A j hA f) ∧
    ((signedMeanSource A j hA).probEvent (L := N)
        (fun ωp : Fin N → I =>
          (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ∨
          (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
              - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|)
      ≤ (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
          / ((N : ℝ)*(nu : ℝ)^2)) := by
  have hnuR : 0 < (nu : ℝ) := by exact_mod_cast hnu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact unknownSigma_failure_bound A j hA f nu eps N h K r hk hN hf hnu hnu1 heps
  · exact unknownSigma_bounded_moments A j hA f hf
  · exact unknownSigma_fourth_moment_ge_variance_sq A j hA f
  · exact unknownSigma_pilot_moment_failure_mass A j hA f N (nu : ℝ) hN hnuR

/-- Under the stated pilot and payoff assumptions, the unknown-variance estimator succeeds with
mass at least 1 − δ whenever (8/9)^r + 2/(Nν²) ≤ δ and 0 < δ < 1 [Montanaro2015]. -/
theorem clause8_success_endpoint
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) ≤ δ) :
    SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
      (fun rec => ¬ unknownSigmaFails A j hA f nu eps N h K r hk rec)
      ≥ 1 - δ :=
  unknownSigma_success_bound A j hA f nu eps N h K r hk hN hf hnu hnu1 heps δ hδ0 hδ1 hδ

/-- Collects normalization, confidence, moment bounds, pathwise worst-case ledger domination,
and the displayed moment-weighted expected-access bound for the unknown-variance mean
estimator under the stated hypotheses [Montanaro2015]. -/
theorem clause8_endpoint
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) ≤ δ) :
    (∑ rec : unknownSigmaFullRecord I N K r,
        (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec) = 1 ∧
    (SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (unknownSigmaFails A j hA f nu eps N h K r hk)
      ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2)) ∧
    (SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (fun rec => ¬ unknownSigmaFails A j hA f nu eps N h K r hk rec) ≥ 1 - δ) ∧
    (unknownSigmaSecondMoment A j hA f ≤ 1 ∧ unknownSigmaFourthMoment A j hA f ≤ 1) ∧
    ((signedMeanSource A j hA).variance (fun i => (f i : ℝ))^2
      ≤ unknownSigmaFourthMoment A j hA f) ∧
    (∀ ωp : Fin N → I, unknownSigmaLedgerLe
        (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp))
        (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps))) ∧
    (unknownSigmaExpectedAccesses A j hA f nu eps N h K r hk
      ≤ unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
              (nu : ℝ) h (eps : ℝ))
        + ((unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
            / ((N : ℝ)*(nu : ℝ)^2)) *
          unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (unknownSigmaLaw A j hA f nu eps N h K r hk).sum_one
  · exact unknownSigma_failure_bound A j hA f nu eps N h K r hk hN hf hnu hnu1 heps
  · exact unknownSigma_success_bound A j hA f nu eps N h K r hk hN hf hnu hnu1 heps
      δ hδ0 hδ1 hδ
  · exact unknownSigma_bounded_moments A j hA f hf
  · exact unknownSigma_fourth_moment_ge_variance_sq A j hA f
  · intro ωp
    exact unknownSigma_budget_worst_path_pilot A j hA f nu eps N h K r hk
      hN hf hnu hnu1 heps ωp
  · exact unknownSigma_expected_accesses_le A j hA f nu eps N h K r hk
      hN hf hnu hnu1 heps

/-- Collects Boolean marking and controlled-phase implementations, single-record and
joint-record oracle-cost transports, expected path-cost identities for approximate and exact
counting, and source ledger relations. It also records failure of unrestricted transport,
the obstruction from zero grids, and existence of path transport for positive grids
[BrassardEtAl2002]. -/
theorem clause84_endpoint
    (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (N : ℕ) (hN : 0 < N) (Sc : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε)
    (hM0 : 2 ≤ exactCountM₀ N)
    (hM : ∀ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) :
    (BooleanEvaluationOracle (preparedMark S) S ∧
      ControlledPhaseImplementation (preparedMark S) S ∧
      (∀ M : ℕ, ∀ hM : 2 ≤ M,
        RecordOracleCostTransport M A j S (preparedMark S) hA hM)) ∧
    (JointRecordOracleCostTransport (basicApproxCountPrefixWeight hN Sc)
        (fun ω => recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
          (basicApproxCountExecFlag N ω)
          (basicApproxCountFinalM ε (basicApproxCountStop N ω)))
        (fun ω => basicApproxCountTotalCost N ε ω) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) * ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ))
        = (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathPrep (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = 2 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathControl (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) * (0 : ℝ)) = 0 ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathFixed (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = 5 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + 3 * ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ)) ∧
    (JointRecordOracleCostTransport (exactCountPathWeight hN Sc hM0)
        (exactCountExecutedGrids N)
        (fun z => 2 * exactCountM₀ N + exactCountGrid N
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) ∧
      (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
          (exactCountPathWeight hN Sc hM0 z) *
            ((2 * exactCountM₀ N + exactCountGrid N
              ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
              ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2) : ℕ) : ℝ))
        = (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
            (exactCountPathWeight hN Sc hM0 z) *
              ((pathMarks (exactCountExecutedGrids N z) : ℕ) : ℝ))
          + ∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
            (exactCountPathWeight hN Sc hM0 z) *
              ((exactCountExecutedGrids N z).length : ℝ)) ∧
    ((∀ M : ℕ, ∀ jj : Fin M,
        RecordLedgerTransport (sourceDepth M jj) (recordLedger (sourceDepth M jj))) ∧
      (∀ M : ℕ, sourceRoundSourceLedger M = sourceRoundControlledMarkLedger M + M)) ∧
    (¬ (∀ (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ),
        (∀ ω, sourceLedger ω =
          (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) →
        JointRecordOracleCostTransport w
          (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
          sourceLedger) ∧
      (∀ grids : List ℕ, 0 ∈ grids →
        ¬ ∃ L : OracleCostLedger, PathLedgerTransport grids L) ∧
      (∀ grids : List ℕ, (∀ g ∈ grids, 1 ≤ g) →
        ∃ L : OracleCostLedger, PathLedgerTransport grids L)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact booleanEvaluationOracle_preparedMark S
    · exact controlledPhaseImplementation_preparedMark S
    · intro M hM
      exact clause89_record A j S (preparedMark S) hA
        (booleanEvaluationOracle_preparedMark S)
        (controlledPhaseImplementation_preparedMark S) M hM
  · have hslots := basicApproxCount_expected_ledger_slots N Sc hN ε hε
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact basicApproxCount_oracle_cost_transport N Sc hN ε hε
    · exact basicApproxCount_expected_source_eq_marks_plus_finals N Sc hN ε hε
    · exact hslots.1
    · exact hslots.2.1
    · exact hslots.2.2.1
    · exact hslots.2.2.2
  · refine ⟨?_, ?_⟩
    · exact exactCount_oracle_cost_transport N Sc hN hM0 hM
    · exact exactCount_expected_source_eq_marks_plus_finals N Sc hN hM0 hM
  · refine ⟨?_, ?_⟩
    · intro M jj
      exact sourceRoundRecord_ledger_transport M jj
    · intro M
      exact sourceRound_ledger_relation M
  · refine ⟨?_, ?_, ?_⟩
    · exact clause89_basic_false
    · intro grids hg
      exact not_pathLedgerTransport_of_zero_mem hg
    · intro grids hg
      exact (pathLedgerTransport_exists_iff grids).2 hg

/-- The record ledger at every source depth satisfies `RecordLedgerTransport` for that depth. -/
theorem s2_source_round_record_ledger_transport (M : ℕ) (jj : Fin M) :
    RecordLedgerTransport (sourceDepth M jj) (recordLedger (sourceDepth M jj)) :=
  sourceRoundRecord_ledger_transport M jj

/-- The source-round source ledger equals its controlled-mark ledger plus the window size M. -/
theorem s2_source_round_ledger_relation (M : ℕ) :
    sourceRoundSourceLedger M = sourceRoundControlledMarkLedger M + M :=
  sourceRound_ledger_relation M

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
