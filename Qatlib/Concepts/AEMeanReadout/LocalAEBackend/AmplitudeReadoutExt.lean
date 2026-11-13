/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ComparativeStrictBounds
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountingOracleTransport
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.EffectiveIntegerReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnknownSigmaMean

/-!
# Search stopping laws and amplitude readout endpoints

This module connects the source search schedule to measured round success, finite-horizon
execution, and unbounded stopping laws. It packages amplitude estimation windows and oracle cost
transport from [BrassardEtAl2002], and pilot-based signed-mean confidence bounds in the setting
of [Montanaro2015]. The search results distinguish the source depth schedule from the shifted
schedule through an explicit boundary correction.

## Main statements

* `clause26_endpoint`: gives positive-mass termination, marked outputs, and unbounded expected
  cost bounds.
* `clause88_endpoint`: collects strict phase, amplitude, and counting success windows.
* `clause21_endpoint`: combines unknown-variance confidence, moment, and resource bounds.
* `clause89_endpoint`: transports single-record and counting-path oracle ledgers.

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

/-- The source round succeeds with its initial marked probability plus its initial failure
probability times the source-window average. -/
theorem s1_source_round_success_mass (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * sourceWindowAverage A j₀ S (qSearchWindow l) :=
  sourceRound_successMass A hA j₀ S l

/-- The shifted search round succeeds with its initial marked probability plus its initial
failure probability times the shifted-window average. -/
theorem s1_frozen_shifted_round_success_mass (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * shiftedWindowAverage A j₀ S (qSearchWindow l) := by
  rw [← shiftedRound_eq_frozenRound A hA j₀ S l]
  exact shiftedRound_successMass A hA j₀ S l

/-- The difference between source and shifted round success masses equals the initial failure
probability times the difference of the two boundary depth masses divided by the window
size. -/
theorem s1_source_schedule_exact_relation_to_frozen_shifted (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      - roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l)
      = (1 - MeasureProb (preparedAAState A j₀) S)
        * ((depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
            / (qSearchWindow l : ℝ)) := by
  rw [← shiftedRound_eq_frozenRound A hA j₀ S l]
  exact sourceRound_successMass_sub_shiftedRound A hA j₀ S l

/-- The source and shifted round success masses differ when their boundary depth masses differ
and the initial marked probability is not one. -/
theorem s1_source_schedule_ne_frozen_shifted_of_boundary (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ)
    (hbound : depthSuccessMass A j₀ S (qSearchWindow l) ≠ depthSuccessMass A j₀ S 0)
    (hA1 : MeasureProb (preparedAAState A j₀) S ≠ 1) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      ≠ roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l) := by
  rw [← shiftedRound_eq_frozenRound A hA j₀ S l]
  exact sourceRound_successMass_ne_shiftedRound_of_boundary A hA j₀ S l hbound hA1

/-- The source and shifted window averages differ by the terminal depth success mass minus the
zero-depth mass, divided by the window size. -/
theorem s1_source_window_average_exact_relation (A : Matrix I I ℂ) (j₀ : I)
    (S : Finset I) (l : ℕ) :
    sourceWindowAverage A j₀ S (qSearchWindow l)
      - shiftedWindowAverage A j₀ S (qSearchWindow l)
      = (depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
          / (qSearchWindow l : ℝ) :=
  sourceWindowAverage_sub_shiftedWindowAverage A j₀ S (qSearchWindow l)
    (qSearchWindow_pos l)

/-- When the initial marked probability is `sin² θ` for an interior angle, the source-window
success sum has the stated closed trigonometric form. -/
theorem s1_source_window_sum_closed (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (l : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    (∑ i : Fin (qSearchWindow l), depthSuccessMass A j₀ S (sourceDepth (qSearchWindow l) i))
      = ((qSearchWindow l + 1 : ℕ) : ℝ) * (1 / 2
          - Real.sin (4 * ((qSearchWindow l + 1 : ℕ) : ℝ) * θ)
            / (4 * ((qSearchWindow l + 1 : ℕ) : ℝ) * Real.sin (2 * θ))) - (Real.sin θ)^2 :=
  sourceWindowSum_closed A j₀ S θ (qSearchWindow l) hA (qSearchWindow_pos l) hθ0 hθ1 hprob

/-- Every successful result in the support of a finite-horizon source search loop belongs to the
marked set. -/
theorem s1_finite_horizon_shape (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    ∀ (T off : ℕ) (out : Option I × ℕ × ℕ),
      out ∈ (sourceQSearchLoop A hA j₀ S T off).support →
      ∀ y, out.1 = some y → y ∈ S :=
  sourceLoop_shape A hA j₀ S

/-- The rational label readout is no greater than the ideal amplitude estimate, and its absolute
error multiplied by `2^b` is strictly less than one. -/
theorem s1_terminating_rational_readout (M : ℕ) (b : ℕ) (z : Fin M) :
    (labelReadout M b z : ℝ) ≤ aeEstimate M z ∧
      |(labelReadout M b z : ℝ) - aeEstimate M z| * (2 : ℝ)^b < 1 := by
  have ha0 : (0:ℝ) ≤ aeEstimate M z := (aeEstimate_mem M z).1
  constructor
  · exact dyadicRound_le b (aeEstimate M z)
  · exact dyadicRound_error b (aeEstimate M z)

/-- Label zero decodes to zero on a positive grid, and dyadic rounding fixes one. -/
theorem s1_terminating_rational_readout_boundaries (M : ℕ) (b : ℕ) (hM : 0 < M) :
    labelReadout M b ⟨0, by omega⟩ = 0 ∧ dyadicRound b 1 = 1 :=
  ⟨by simp [labelReadout, aeEstimate, dyadicRound_zero], dyadicRound_one b⟩

/-- The nearest-integer count readout is at most `N` and differs from the ideal scaled estimate
by at most one half. -/
theorem s1_effective_integer_readout (N M : ℕ) (z : Fin M) :
    countLabelReadoutNearest N M z ≤ N ∧
      |(countLabelReadoutNearest N M z : ℝ) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 :=
  ⟨countLabelReadoutNearest_le N M z, countLabelReadoutNearest_error N M z⟩

/-- The nearest-integer readout rounds half-integers upward, and the floor count readout
preserves exact integer scaled estimates. -/
theorem s1_effective_integer_readout_boundaries (N M : ℕ) (z : Fin M) (k : ℕ) :
    (∀ h : (N : ℝ) * aeEstimate M z = (k : ℝ) + 1 / 2,
        countLabelReadoutNearest N M z = k + 1) ∧
      (∀ h : (N : ℝ) * aeEstimate M z = (k : ℝ), countLabelReadout N M z = k) := by
  constructor
  · intro h
    exact countLabelReadoutNearest_tie N M z k h
  · intro h
    exact countLabelReadout_exact N M z k h

/-- For positive initial marked probability, the source search survival probability tends to
zero. -/
theorem s1_unbounded_process_terminates (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Tendsto (sourceSurvival A hA j₀ S) atTop (𝓝 0) :=
  sourceSurvival_tendsto_zero A hA j₀ S ha

/-- For zero initial marked probability, the source search survival probability is one at every
horizon. -/
theorem s1_unbounded_process_never_halts (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    ∀ n, sourceSurvival A hA j₀ S n = 1 :=
  sourceSurvival_eq_one_of_zero A hA j₀ S ha

/-- Every successful halting configuration in the support of a source transition returns a
marked element. -/
theorem s1_unbounded_process_halts_marked (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r c1 c2 : ℕ) (cfg : Configuration SourceRunState (SourceRunOutcome I))
    (hcfg : cfg ∈ (sourceTransition A hA j₀ S r c1 c2).support) :
    ∀ y c1' c2', cfg = Sum.inl (some y, c1', c2') → y ∈ S :=
  sourceTransition_halt_marked A hA j₀ S r c1 c2 cfg hcfg

/-- For positive initial marked probability, the stopping law assigns each round its specified
first-stop mass. -/
theorem s1_unbounded_stopping_law (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    ∀ k, sourceStopLaw A hA j₀ S ha k = sourceStopMass A hA j₀ S k :=
  sourceStopLaw_mass A hA j₀ S ha

/-- The sum of the first `N` stopping masses plus survival through `N` rounds equals one. -/
theorem s1_unbounded_stopping_telescopes (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (N : ℕ) :
    (∑ k ∈ Finset.range N, sourceStopMass A hA j₀ S k)
      + sourceSurvival A hA j₀ S N = 1 :=
  sum_sourceStopMass_add_survival A hA j₀ S N

/-- For zero initial marked probability, the first-stop mass of every round is zero. -/
theorem s1_unbounded_no_halt_round_at_zero (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) (k : ℕ) :
    sourceStopMass A hA j₀ S k = 0 :=
  sourceStopMass_zero A hA j₀ S ha k

/-- The expected first ledger component of the truncated source search is nondecreasing when the
horizon increases by one. -/
theorem s1_cumulative_ledger_expectation_mono (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S (T+1) 0)
          (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceLoop_ledger1_expectation_mono A hA j₀ S T

/-- The expected second ledger component of the truncated source search is nondecreasing when
the horizon increases by one. -/
theorem s1_cumulative_chi_expectation_mono (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S (T+1) 0)
          (fun out => (out.2.2 : ℝ≥0∞)) :=
  sourceLoop_ledger2_expectation_mono A hA j₀ S T

/-- The first accumulated ledger expectation after `N` unbounded-process steps equals that of
the `N`-round truncated source loop. -/
theorem s1_unbounded_execution_matches_truncated_loop (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (N : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N (sourceInitial (I := I)))
        (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S N 0)
          (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceRunFor_ledger_eq_sourceLoop A hA j₀ S (fun c1 c2 => c1)
    (fun _ _ _ _ => rfl) (by rfl) N

/-- The truncated loop's first ledger expectation is the sum of each round's expected cost
weighted by its reach mass. -/
theorem s1_cumulative_ledger_expectation_unfold (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
            (fun out => (out.2.1 : ℝ≥0∞)) :=
  sourceQSearchLoop_ledger_expectation_unfold A hA j₀ S
    (fun out => (out.2.1 : ℝ≥0∞)) (fun _ out => by simp only []; rw [Nat.cast_add])
    (by simp) T

/-- The first accumulated ledger expectations of finite executions converge to the source
stopping-ledger expectation. -/
theorem s1_stop_cost_expectation_is_limit (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    Tendsto (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
        (sourceInitial (I := I)))
        (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞)))
      atTop (𝓝 (sourceStopLedgerExpectation A hA j₀ S
        (fun out => (out.2.1 : ℝ≥0∞)))) :=
  sourceStopLedgerExpectation_eq_limit A hA j₀ S (fun c1 c2 => c1)
    (fun _ _ _ _ => rfl) (by rfl)

/-- For an interior angle with marked probability `sin² θ`, a source round satisfying
`(qSearchWindow l+1)*sin(2*θ) ≥ 1` has failure probability at most `3/4`. -/
theorem s1_mature_source_round_fails_at_most_three_quarters (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) * Real.sin (2 * θ)) :
    1 - roundSuccessMass (sourceQSearchRound A hA j₀ S l) ≤ 3 / 4 :=
  sourceRound_fail_prob_le_three_quarters A hA j₀ S θ l hθ0 hθ1 hprob hmature

/-- The two source-round ledger expectations are at most `6*(6/5)^l` and `4*(6/5)^l`,
respectively. -/
theorem s1_source_round_ledger_cost (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) :=
  ⟨sourceRound_ledger1_expectation_le A hA j₀ S l,
    sourceRound_ledger2_expectation_le A hA j₀ S l⟩

/-- For positive initial marked probability `a`, both ledger expectations of every truncated
source search are at most `400/√a`. -/
theorem s1_source_search_two_ledger_budget (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
  ⟨sourceLoop_ledger1_expectation_le A hA j₀ S T ha,
    sourceLoop_ledger2_expectation_le A hA j₀ S T ha⟩

/-- For positive initial marked probability `a`, both unbounded stopping-ledger expectations are
at most `400/√a`. -/
theorem s1_unbounded_stop_cost_retains_sqrt_a_budget (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
  sourceStopLedgerExpectation_le A hA j₀ S ha

/-- Collects effective rational and integer decoding bounds, half-up boundary behavior,
agreement with `aeEffCount`, bit and space budget inequalities, and effective integer
readout transport [BrassardEtAl2002]. -/
theorem clause90_endpoint :

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

/-- Collects the source depth schedule, round and finite-horizon ledger bounds, its boundary
correction relative to the shifted schedule, and survival at zero marked probability
[BrassardEtAl2002]. -/
theorem clause5_endpoint :

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
    exact s1_source_round_ledger_cost A hA j₀ S l
  · intro A hA j₀ S T ha
    exact s1_source_search_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S l
    exact s1_source_schedule_exact_relation_to_frozen_shifted A hA j₀ S l
  · intro A hA j₀ S T ha
    exact source_and_shifted_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S ha n
    exact s1_unbounded_process_never_halts A hA j₀ S ha n

/-- Collects termination for positive marked probability, correctness of successful halts,
convergence of accumulated expected costs, and the two `400/√a` stopping-cost bounds. At
zero marked probability, survival remains one [BrassardEtAl2002]. -/
theorem clause26_endpoint :

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
    exact s1_unbounded_process_terminates A hA j₀ S ha
  · intro A hA j₀ S r c1 c2 cfg hcfg
    exact s1_unbounded_process_halts_marked A hA j₀ S r c1 c2 cfg hcfg
  · intro A hA j₀ S
    exact s1_stop_cost_expectation_is_limit A hA j₀ S
  · intro A hA j₀ S ha
    exact s1_unbounded_stop_cost_retains_sqrt_a_budget A hA j₀ S ha
  · intro A hA j₀ S ha n
    exact s1_unbounded_process_never_halts A hA j₀ S ha n

/-- Collects strict phase, amplitude, and cardinality estimation windows with mass greater than
`1 - 1/(2*(k-1))`, including endpoint and odd-grid specializations [BrassardEtAl2002]. -/
theorem clause88_endpoint :

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
    exact bhmt11WindowMass_strict M ω hM k hk
  · intro M A j S hM hA k hk
    exact preparedAeWindow_strict M A j S hM hA k hk
  · intro N M S hN hM k hk
    exact countingWindow_strict N M S hN hM k hk
  · intro M A j S hM hA k hk ha
    exact preparedAeWindow_strict M A j S hM hA k hk
  · intro M A j S hM hA k hk ha
    exact preparedAeWindow_strict M A j S hM hA k hk
  · intro M A j S hM hA k hk hodd
    exact preparedAeWindow_strict M A j S hM hA k hk

/-- For a rational payoff bounded in absolute value by one, the unknown-variance failure mass is
at most `(8/9)^r + 2/(N*nu²)`. The second and fourth moments, squared variance, and pilot
deviation probability satisfy the stated moment bounds [Montanaro2015]. -/
theorem clause21_confidence_endpoint
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

/-- If the unknown-variance failure bound is at most `δ`, the complement of `unknownSigmaFails`
has mass at least `1-δ`. -/
theorem clause21_success_endpoint
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

/-- For a bounded rational payoff and the stated confidence parameters, the unknown-variance
record law is normalized and has success mass at least `1-δ`. It also satisfies the moment,
worst-precision ledger, and expected-access bounds [Montanaro2015]. -/
theorem clause21_endpoint
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

/-- Collects prepared marking validation, single-record cost transport, basic and exact counting
path identities, and source-round conservation. It also records the obstruction from zero
grids and existence of path ledgers for positive grids [BrassardEtAl2002]. -/
theorem clause89_endpoint
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

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
