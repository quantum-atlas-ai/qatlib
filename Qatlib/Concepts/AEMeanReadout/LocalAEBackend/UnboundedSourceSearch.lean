/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop

/-!
# Survival and stopping laws for source search

This module gives the source-search loop an unbounded transition semantics with two accumulated
cost counters. For positive initial marked mass, `sourceSurvival_tendsto_zero` and
`sourceStopLaw` express eventual termination; finite-loop expectations are expanded using reach
probabilities in the search setting of [BrassardEtAl2002].

## Main statements

* `sourceSurvival_tendsto_zero`: vanishing survival probability for positive marked mass.
* `sourceStopLaw`: the normalized stopping-index law.
* `sourceRunFor_ledger_eq_loop`: agreement of transition-run and finite-loop cost expectations.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
set_option warningAsError false

/-- The running search state, consisting of the round index and two accumulated cost counters. -/
abbrev SourceRunState := ℕ × ℕ × ℕ

/-- The halted search outcome, consisting of an optional output label and two accumulated cost
counters. -/
abbrev SourceRunOutcome (I : Type) := Option I × ℕ × ℕ

/-- The one-round transition law that halts on a successful output and otherwise advances the
round index, adding both round costs. -/
noncomputable def sourceTransition {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r : ℕ) (c1 c2 : ℕ) : PMF (Configuration SourceRunState (SourceRunOutcome I)) :=
  PMF.map (fun out =>
      if out.1.isSome then Sum.inl (out.1, c1 + out.2.1, c2 + out.2.2)
      else Sum.inr (r + 1, c1 + out.2.1, c2 + out.2.2))
    (sourceQSearchRound A hA j₀ S r)

/-- The source-search transition kernel obtained by unpacking the round index and accumulated
counters. -/
noncomputable def sourceNext {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    SourceRunState → PMF (Configuration SourceRunState (SourceRunOutcome I)) :=
  fun st => sourceTransition A hA j₀ S st.1 st.2.1 st.2.2

/-- The initial running configuration at round one with both cost counters zero. -/
noncomputable def sourceInitial {I : Type} [Fintype I] [DecidableEq I] :
    Configuration SourceRunState (SourceRunOutcome I) :=
  Sum.inr (1, 0, 0)

/-- Every supported halted transition carrying `some y` has `y ∈ S`. -/
theorem sourceTransition_halt_marked {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r c1 c2 : ℕ) (cfg : Configuration SourceRunState (SourceRunOutcome I))
    (hcfg : cfg ∈ (sourceTransition A hA j₀ S r c1 c2).support) :
    ∀ y c1' c2', cfg = Sum.inl (some y, c1', c2') → y ∈ S := by
  rw [sourceTransition] at hcfg
  obtain ⟨out, hout, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hcfg
  have hshape := windowRound_shape A hA j₀ S (qSearchWindow r) (qSearchWindow_pos r)
    (fun j => preparedAATrial A hA j₀ S
      (⟨sourceDepth (qSearchWindow r) j, by omega⟩
        : Fin (sourceDepth (qSearchWindow r) j + 1)))
    (fun j => (2 + 2 * sourceDepth (qSearchWindow r) j, 2 + sourceDepth (qSearchWindow r) j))
    out hout
  intro y c1' c2' heqcfg
  rcases Option.eq_none_or_eq_some out.1 with hnone | ⟨y0, hy0⟩
  · rw [hnone, Option.isSome_none] at heq
    exact (Sum.inl_ne_inr ((heq.trans heqcfg).symm)).elim
  · rw [hy0, Option.isSome_some] at heq
    have hy0y : y0 = y := by
      have h := congrArg (fun z : Configuration SourceRunState (SourceRunOutcome I) =>
        match z with
        | Sum.inl p => p.1
        | Sum.inr _ => none) (heq.trans heqcfg)
      have h' : some y0 = some y := by simpa using! h
      exact Option.some.inj h'
    rw [← hy0y]
    exact hshape y0 hy0

/-- The probability that a transition remains running equals the failure probability of its
source-search round. -/
theorem sourceTransition_running_mass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r c1 c2 : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceTransition A hA j₀ S r c1 c2) (fun cfg => ∃ u, cfg = Sum.inr u)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S r) (fun out => out.1 = none) := by
  rw [sourceTransition, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro out
  rcases Option.eq_none_or_eq_some out.1 with hnone | ⟨y0, hy0⟩
  · rw [hnone, Option.isSome_none]
    simp
  · rw [hy0, Option.isSome_some]
    simp

/-- The source-round failure mass is at most one minus the initial marked mass. -/
theorem sourceRound_fail_mass_le (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ 1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  have hpart := event_compl (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
  have hcongr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ¬ ∃ y, out.1 = some y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun out => by
      constructor
      · intro h
        cases ho : out.1 with
        | none => rfl
        | some y => exact absurd ⟨y, ho⟩ h
      · intro h hex
        obtain ⟨y, hy⟩ := hex
        rw [h] at hy
        exact absurd hy (by simp))
  rw [hcongr] at hpart
  have hge : ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y) := by
    rw [sourceRound_success_mass]
    have hnonneg : 0 ≤ (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S))
        * (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (depthSuccessMass A j₀ S (sourceDepth (qSearchWindow l) j))) := by
      positivity
    exact le_add_of_nonneg_right hnonneg
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
    ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
        add_le_add hge (le_refl _)
    _ = 1 := hpart

/-- Every fixed-depth amplified success mass is zero if the initial marked mass is zero. -/
theorem depthSuccessMass_eq_zero_of_zero (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (k : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    depthSuccessMass A j₀ S k = 0 := by
  unfold depthSuccessMass
  rw [(prepared_aa_endpoint_states A j₀ S k hA).1 ha, ha]

/-- A source-search round has zero success probability if the initial marked mass is zero. -/
theorem sourceRound_success_mass_zero (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y) = 0 := by
  rw [sourceRound_success_mass]
  have hsum : ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
      (depthSuccessMass A j₀ S (sourceDepth (qSearchWindow l) j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _jmem
    rw [depthSuccessMass_eq_zero_of_zero A j₀ S (sourceDepth (qSearchWindow l) j) hA ha,
      ENNReal.ofReal_zero]
  rw [ha, ENNReal.ofReal_zero, hsum]
  simp

/-- The probability that source search is still running after `n` transitions from its initial
configuration. -/
noncomputable def sourceSurvival {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (n : ℕ) : ℝ≥0∞ :=
  finiteSurvival (sourceNext A hA j₀ S) n (sourceInitial (I := I))

/-- The survival probability after `n` transitions is at most `(1 - a)^n`, embedded in extended
nonnegative reals, for initial marked mass `a`. -/
theorem sourceSurvival_le_pow {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (n : ℕ) :
    sourceSurvival A hA j₀ S n
      ≤ (ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S)) ^ n := by
  have ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S := measureProb_nonneg _ _
  have ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S
  refine (finite_survival_geometric_bound (sourceNext A hA j₀ S) (1, 0, 0)
    (ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S)) n ?_ ?_).1
  · rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro t
    rw [sourceNext, sourceTransition_running_mass]
    have hbound := sourceRound_fail_mass_le A hA j₀ S t.1
    have hq : 1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        = ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S) := by
      rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_sub 1 ha0]
    rw [hq] at hbound
    exact hbound

/-- For positive initial marked mass, the source-search survival probability tends to zero. -/
theorem sourceSurvival_tendsto_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Tendsto (sourceSurvival A hA j₀ S) atTop (𝓝 0) := by
  have ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S
  have hqlt : ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S) < (1 : ℝ≥0∞) := by
    rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)]
    linarith
  have hpow : Tendsto (fun n : ℕ =>
      (ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S)) ^ n)
      atTop (𝓝 0) := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hqlt
  refine Filter.Tendsto.squeeze' (tendsto_const_nhds) hpow ?_ ?_
  · filter_upwards [] with n
    exact bot_le
  · filter_upwards [] with n
    exact sourceSurvival_le_pow A hA j₀ S n

/-- For zero initial marked mass, the source-search survival probability is one at every finite
horizon. -/
theorem sourceSurvival_eq_one_of_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    ∀ n, sourceSurvival A hA j₀ S n = 1 := by
  have hmain : ∀ (n : ℕ) (u : SourceRunState),
      finiteSurvival (sourceNext A hA j₀ S) n (Sum.inr u) = 1 := by
    intro n
    induction n with
    | zero =>
        intro u
        exact finiteSurvival_zero_running _ _
    | succ n ih =>
        intro u
        rw [finiteSurvival_succ_running]
        have hsucc0 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S u.1)
            (fun out => ∃ y, out.1 = some y) = 0 :=
          sourceRound_success_mass_zero A hA j₀ S u.1 ha
        have hnone : ∀ out ∈ (sourceQSearchRound A hA j₀ S u.1).support, out.1 = none := by
          intro out hout
          have hne : (sourceQSearchRound A hA j₀ S u.1) out ≠ 0 :=
            (PMF.mem_support_iff _ _).mp hout
          have hz : ∀ x, (sourceQSearchRound A hA j₀ S u.1) x
              * (if ∃ y, x.1 = some y then 1 else 0) = 0 := by
            intro x
            have h := ENNReal.tsum_eq_zero.mp hsucc0 x
            simpa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event] using! h
          by_cases hsucc : ∃ y, out.1 = some y
          · have hzout := hz out
            rw [if_pos hsucc, mul_one] at hzout
            exact (hne hzout).elim
          · rcases Option.eq_none_or_eq_some out.1 with hn | ⟨y0, hy0⟩
            · exact hn
            · exact absurd ⟨y0, hy0⟩ hsucc
        have hnohalt : ∀ cfg ∈ (sourceNext A hA j₀ S u).support, ∃ v, cfg = Sum.inr v := by
          intro cfg hcfg
          rw [sourceNext, sourceTransition] at hcfg
          obtain ⟨out, hout, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hcfg
          have houtnone : out.1 = none := hnone out hout
          rw [houtnone, Option.isSome_none] at heq
          exact ⟨_, heq.symm⟩
        have hone : ∀ cfg ∈ (sourceNext A hA j₀ S u).support,
            finiteSurvival (sourceNext A hA j₀ S) n cfg = 1 := by
          intro cfg hcfg
          obtain ⟨v, hv⟩ := hnohalt cfg hcfg
          rw [hv]
          exact ih v
        have hkey : ∀ cfg, (sourceNext A hA j₀ S u) cfg
            * finiteSurvival (sourceNext A hA j₀ S) n cfg
            = (sourceNext A hA j₀ S u) cfg := by
          intro cfg
          by_cases h : cfg ∈ (sourceNext A hA j₀ S u).support
          · rw [hone cfg h, mul_one]
          · have hp : (sourceNext A hA j₀ S u) cfg = 0 := by
              simpa [PMF.mem_support_iff] using! h
            rw [hp, zero_mul]
        show ∑' cfg, (sourceNext A hA j₀ S u) cfg
            * finiteSurvival (sourceNext A hA j₀ S) n cfg = 1
        rw [tsum_congr hkey]
        simp [PMF.tsum_coe]
  intro n
  exact hmain n (1, 0, 0)

/-- The stopping mass at index `k`, defined as survival at `k` minus survival at `k + 1`. -/
noncomputable def sourceStopMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (k : ℕ) : ℝ≥0∞ :=
  sourceSurvival A hA j₀ S k - sourceSurvival A hA j₀ S (k + 1)

/-- Within a finite run of at least `k ≥ 1` steps, the probability of first halting at step `k`
equals `sourceStopMass` at index `k - 1`. -/
theorem sourceStopMass_eq_first_stop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (fuel k : ℕ) (hk : 1 ≤ k) (hkf : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (sourceNext A hA j₀ S) fuel (sourceInitial (I := I)))
        (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = k)
      = sourceStopMass A hA j₀ S (k - 1) := by
  have h := finite_first_stop_mass (sourceNext A hA j₀ S) (1, 0, 0) fuel k hk hkf
  simp only [sourceStopMass, sourceSurvival]
  rw [Nat.sub_add_cancel hk]
  exact h

/-- The stopping masses before horizon `N` plus the survival mass at `N` sum to one. -/
theorem sum_sourceStopMass_add_survival {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, sourceStopMass A hA j₀ S k)
      + sourceSurvival A hA j₀ S N = 1 := by
  have hstep : ∀ k : ℕ,
      sourceStopMass A hA j₀ S k + sourceSurvival A hA j₀ S (k + 1)
        = sourceSurvival A hA j₀ S k := by
    intro k
    have hle : sourceSurvival A hA j₀ S (k + 1) ≤ sourceSurvival A hA j₀ S k :=
      finiteSurvival_succ_le (sourceNext A hA j₀ S) k (sourceInitial (I := I))
    rw [sourceStopMass, tsub_add_cancel_of_le hle]
  induction N with
  | zero =>
      have hz : sourceSurvival A hA j₀ S 0 = 1 :=
        finiteSurvival_zero_running (sourceNext A hA j₀ S) (1, 0, 0)
      simp [hz]
  | succ N ih =>
      have hsum := Finset.sum_range_succ (sourceStopMass A hA j₀ S) N
      rw [hsum, add_assoc, hstep N, ih]

/-- The probability mass function on stopping indices obtained from `sourceStopMass` when the
initial marked mass is positive. -/
noncomputable def sourceStopLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) : PMF ℕ :=
  ⟨fun k => sourceStopMass A hA j₀ S k,
    ENNReal.hasSum_iff_tendsto_nat 1 |>.2 (by
      have hsub : ∀ N : ℕ, (∑ k ∈ Finset.range N, sourceStopMass A hA j₀ S k)
          = 1 - sourceSurvival A hA j₀ S N := by
        intro N
        have hne : sourceSurvival A hA j₀ S N ≠ ∞ := by
          intro h
          have hle : sourceSurvival A hA j₀ S N ≤ 1 := by
            exact finiteSurvival_le_one (sourceNext A hA j₀ S) N (sourceInitial (I := I))
          rw [h] at hle
          exact absurd hle (by simp)
        refine ENNReal.eq_sub_of_add_eq hne ?_
        exact sum_sourceStopMass_add_survival A hA j₀ S N
      have hfun : (fun N : ℕ => ∑ i ∈ Finset.range N, sourceStopMass A hA j₀ S i)
          = fun N : ℕ => 1 - sourceSurvival A hA j₀ S N := by
        funext N
        exact hsub N
      rw [hfun]
      simpa using! ENNReal.Tendsto.sub (tendsto_const_nhds)
        (sourceSurvival_tendsto_zero A hA j₀ S ha) (Or.inl ENNReal.one_ne_top))⟩

/-- The stopping-index law assigns index `k` exactly the mass `sourceStopMass` at `k`. -/
theorem sourceStopLaw_mass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) (k : ℕ) :
    sourceStopLaw A hA j₀ S ha k = sourceStopMass A hA j₀ S k :=
  rfl

/-- Every stopping mass is zero when the initial marked mass is zero. -/
theorem sourceStopMass_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) (k : ℕ) :
    sourceStopMass A hA j₀ S k = 0 := by
  rw [sourceStopMass, sourceSurvival_eq_one_of_zero A hA j₀ S ha,
    sourceSurvival_eq_one_of_zero A hA j₀ S ha]
  simp

/-- For an additive cost ledger, the finite-loop expectation is the first-round expectation plus
the first-round failure mass times the continuation expectation. -/
theorem windowLoop_ledger_expectation_succ {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (T off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round (T+1) off) L
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off+1)) L
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off+1)) L := by
  rw [windowLoop_succ_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ out : Option I × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (match out.1 with
            | some _ => PMF.pure out
            | none => (windowLoop A hA j₀ S round T (off+1)).map
                (fun r => (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)))
          L
        = L out
          + (if out.1 = none then
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off+1)) L
            else 0) := by
    intro out
    obtain ⟨o1, o2, o3⟩ := out
    cases o1 with
    | none =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (PMF.map (fun r => (r.1, r.2.1 + o2, r.2.2 + o3))
              (windowLoop A hA j₀ S round T (off+1)))
            L
          = L (none, o2, o3)
            + (if (none : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off+1)) L
              else 0)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
          Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr (fun r => hL r (none, o2, o3)),
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const, if_pos rfl]
        ring
    | some y =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.pure (some y, o2, o3)) L
          = L (some y, o2, o3)
            + (if (some y : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off+1)) L
              else 0)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_neg (by simp)]
        ring
  have hcongr :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1)) (fun a =>
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (match a.1 with
              | some _ => PMF.pure a
              | none => PMF.map (fun r => (r.1, r.2.1 + a.2.1, r.2.2 + a.2.2))
                  (windowLoop A hA j₀ S round T (off + 1))) L)
        = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1)) (fun a =>
            L a + (if a.1 = none then
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off + 1)) L else 0)) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit
  trans Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1)) (fun a =>
      L a + (if a.1 = none then
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off + 1)) L else 0))
  · exact hcongr
  · rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, expectation_indicator_mul']
    ring

/-- The first cost counter of a search output, embedded in extended nonnegative reals. -/
noncomputable def ledger1 {I : Type} (out : Option I × ℕ × ℕ) : ℝ≥0∞ :=
  (out.2.1 : ℝ≥0∞)

/-- The second cost counter of a search output, embedded in extended nonnegative reals. -/
noncomputable def ledger2 {I : Type} (out : Option I × ℕ × ℕ) : ℝ≥0∞ :=
  (out.2.2 : ℝ≥0∞)

/-- The first ledger is additive when two pairs of cost counters are added. -/
theorem ledger1_add {I : Type} (r out : Option I × ℕ × ℕ) :
    ledger1 (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = ledger1 r + ledger1 out := by
  obtain ⟨_, r2, _⟩ := r
  obtain ⟨_, o2, _⟩ := out
  simp [ledger1, Nat.cast_add]

/-- The second ledger is additive when two pairs of cost counters are added. -/
theorem ledger2_add {I : Type} (r out : Option I × ℕ × ℕ) :
    ledger2 (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = ledger2 r + ledger2 out := by
  obtain ⟨_, r2, _⟩ := r
  obtain ⟨_, o2, _⟩ := out
  simp [ledger2, Nat.cast_add]

/-- The first ledger vanishes on the output with no result and two zero costs. -/
theorem ledger1_zero {I : Type} : ledger1 ((none : Option I), 0, 0) = 0 := by simp [ledger1]

/-- The second ledger vanishes on the output with no result and two zero costs. -/
theorem ledger2_zero {I : Type} : ledger2 ((none : Option I), 0, 0) = 0 := by simp [ledger2]

/-- The expectation of an additive ledger vanishing at zero is nondecreasing as the loop horizon
increases by one. -/
theorem windowLoop_ledger_expectation_mono {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0) :
    ∀ T off,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T off) L
        ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round (T+1) off) L := by
  intro T
  induction T with
  | zero =>
      intro off
      have hz : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round 0 off) L = 0 := by
        rw [windowLoop_zero_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
        exact hL0
      have hnonneg : (0:ℝ≥0∞)
          ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round 1 off) L := by
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
            ENNReal.tsum_eq_iSup_sum]
        refine le_iSup_of_le (∅ : Finset (Option I × ℕ × ℕ)) ?_
        simp
      exact hz ▸ hnonneg
  | succ T ih =>
      intro off
      have hrec1 := windowLoop_ledger_expectation_succ A hA j₀ S round L hL T off
      have hrec2 := windowLoop_ledger_expectation_succ A hA j₀ S round L hL (T+1) off
      rw [hrec1, hrec2]
      have hmul : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T (off+1)) L
        ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round (T+1) (off+1)) L := by
        exact mul_le_mul_of_nonneg_left (ih (off+1)) (by positivity)
      exact add_le_add_right hmul
          (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off+1)) L)

/-- The expected first cost counter of source search is nondecreasing in the finite horizon. -/
theorem sourceLoop_ledger1_expectation_mono {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S (T+1) 0)
          (fun out => (out.2.1 : ℝ≥0∞)) := by
  have h := windowLoop_ledger_expectation_mono A hA j₀ S (sourceQSearchRound A hA j₀ S)
    (fun out => (out.2.1 : ℝ≥0∞)) (by
      intro r out
      obtain ⟨_, r2, _⟩ := r
      obtain ⟨_, o2, _⟩ := out
      simp [Nat.cast_add]) (by simp) T 0
  exact h

/-- The expected second cost counter of source search is nondecreasing in the finite horizon. -/
theorem sourceLoop_ledger2_expectation_mono {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S (T+1) 0)
          (fun out => (out.2.2 : ℝ≥0∞)) := by
  have h := windowLoop_ledger_expectation_mono A hA j₀ S (sourceQSearchRound A hA j₀ S)
    (fun out => (out.2.2 : ℝ≥0∞)) (by
      intro r out
      obtain ⟨_, r2, _⟩ := r
      obtain ⟨_, o2, _⟩ := out
      simp [Nat.cast_add]) (by simp) T 0
  exact h

/-- The failure probability of source-search round `l`. -/
noncomputable def sourceFailMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (l : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)

/-- The product of `n` consecutive failure masses starting at round `r`, defined recursively. -/
noncomputable def reachMass (fail : ℕ → ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | r, 0 => 1
  | r, n + 1 => fail r * reachMass fail (r + 1) n

/-- The reach mass for `n + 1` rounds factors into failure at the first round and reach mass for
the remaining rounds. -/
theorem reachMass_succ (fail : ℕ → ℝ≥0∞) (r n : ℕ) :
    reachMass fail r (n + 1) = fail r * reachMass fail (r + 1) n := rfl

/-- The reach mass for zero rounds is one. -/
theorem reachMass_zero (fail : ℕ → ℝ≥0∞) (r : ℕ) : reachMass fail r 0 = 1 := rfl

/-- The product of the source-search failure probabilities for `n` rounds starting at `r`. -/
noncomputable def sourceReachFrom {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r n : ℕ) : ℝ≥0∞ :=
  reachMass (sourceFailMass A hA j₀ S) r n

/-- The source reach probability for `n + 1` rounds factors into the first failure mass and the
remaining reach probability. -/
theorem sourceReachFrom_succ {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (r n : ℕ) :
    sourceReachFrom A hA j₀ S r (n + 1)
      = sourceFailMass A hA j₀ S r * sourceReachFrom A hA j₀ S (r + 1) n := by
  unfold sourceReachFrom
  rw [reachMass_succ]

/-- The source reach probability from round one through `k` failures. -/
noncomputable def sourceReachMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (k : ℕ) : ℝ≥0∞ :=
  sourceReachFrom A hA j₀ S 1 k

/-- Survival for `n` transitions from any running state equals the corresponding source reach
probability and does not depend on the accumulated costs. -/
theorem sourceSurvival_eq_reachFrom {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    ∀ (n : ℕ) (r c1 c2 : ℕ),
      finiteSurvival (sourceNext A hA j₀ S) n (Sum.inr (r, c1, c2))
        = sourceReachFrom A hA j₀ S r n := by
  intro n
  induction n with
  | zero =>
      intro r c1 c2
      rw [finiteSurvival_zero_running]
      simp [sourceReachFrom, reachMass_zero]
  | succ n ih =>
      intro r c1 c2
      rw [finiteSurvival_succ_running]
      change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceTransition A hA j₀ S r c1 c2)
          (fun cfg => finiteSurvival (sourceNext A hA j₀ S) n cfg)
        = sourceReachFrom A hA j₀ S r (n + 1)
      rw [sourceTransition, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      have hsplit : ∀ out : Option I × ℕ × ℕ,
          finiteSurvival (sourceNext A hA j₀ S) n
              (if out.1.isSome then Sum.inl (out.1, c1 + out.2.1, c2 + out.2.2)
               else Sum.inr (r + 1, c1 + out.2.1, c2 + out.2.2))
            = if out.1 = none then sourceReachFrom A hA j₀ S (r + 1) n else 0 := by
        intro out
        rcases Option.eq_none_or_eq_some out.1 with hnone | ⟨y0, hy0⟩
        · rw [hnone, Option.isSome_none]
          rw [if_neg (by simp), ih (r + 1) (c1 + out.2.1) (c2 + out.2.2), if_pos rfl]
        · rw [hy0, Option.isSome_some]
          rw [if_pos (by simp), finiteSurvival_halted, if_neg (by simp)]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit,
          expectation_indicator_mul']
      rw [sourceReachFrom_succ A hA j₀ S r n]
      exact mul_comm _ _

/-- Survival from the initial configuration equals `sourceReachMass`. -/
theorem sourceSurvival_eq_reachMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (n : ℕ) :
    sourceSurvival A hA j₀ S n = sourceReachMass A hA j₀ S n := by
  rw [sourceSurvival, sourceReachMass]
  exact sourceSurvival_eq_reachFrom A hA j₀ S n 1 0 0

/-- Expands a finite-loop additive-ledger expectation as the sum of round expectations weighted
by the probabilities of reaching those rounds. -/
theorem windowLoop_ledger_expectation_unfold {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0)
    (fail : ℕ → ℝ≥0∞)
    (hfail : ∀ l : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => out.1 = none) = fail l) :
    ∀ T off,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S round T off) L
        = ∑ i ∈ Finset.range T,
            reachMass fail (off + 1) i
              * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1 + i)) L := by
  intro T
  induction T with
  | zero =>
      intro off
      rw [windowLoop_zero_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      simp [hL0]
  | succ T ih =>
      intro off
      rw [windowLoop_ledger_expectation_succ A hA j₀ S round L hL T off, ih, hfail]
      rw [Finset.sum_range_succ']
      have hidx : ∀ i : ℕ, (off + 1) + 1 + i = off + 1 + (i + 1) := by
        intro i
        omega
      have hstep : ∀ i ∈ Finset.range T,
          reachMass fail (off + 1) (i + 1)
              * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1 + (i + 1))) L
            = fail (off + 1)
              * (reachMass fail (off + 2) i
                * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1 + (i + 1))) L) := by
        intro i _
        rw [reachMass_succ]
        ring
      have hstep2 : ∀ i ∈ Finset.range T,
          reachMass fail (off + 2) i
              * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round ((off + 1) + 1 + i)) L
            = reachMass fail (off + 2) i
              * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off + 1 + (i + 1))) L := by
        intro i _
        rw [hidx i]
      rw [Finset.sum_congr rfl hstep2, Finset.sum_congr rfl hstep]
      rw [reachMass_zero, one_mul]
      simp only [Nat.add_zero]
      rw [Finset.mul_sum]
      ring

/-- Applies an accumulation function to the two cost counters in either a halted or a running
configuration. -/
def sourceAccumulated {I : Type} (acc : ℕ → ℕ → ℕ)
    (cfg : Configuration SourceRunState (SourceRunOutcome I)) : ℕ :=
  match cfg with
  | Sum.inl a => acc a.2.1 a.2.2
  | Sum.inr s => acc s.2.1 s.2.2

/-- For an additive accumulator vanishing at zero, the transition-run expectation equals the
initial accumulated cost plus the corresponding finite-loop cost expectation. -/
theorem sourceRunFor_ledger_eq_loop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (acc : ℕ → ℕ → ℕ)
    (hacc : ∀ a b c d : ℕ, acc (a + c) (b + d) = acc a b + acc c d)
    (hacc0 : acc 0 0 = 0) :
    ∀ (N off c1 c2 : ℕ),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N (Sum.inr (off + 1, c1, c2)))
          (fun x => (sourceAccumulated acc x.1 : ℝ≥0∞))
        = (acc c1 c2 : ℝ≥0∞)
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) N off)
            (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)) := by
  intro N off c1 c2
  induction N generalizing off c1 c2 with
  | zero =>
      rw [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, windowLoop_zero_eq,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      simp only [sourceAccumulated]
      simp [hacc0]
  | succ N ih =>
      have hL : ∀ (r out : Option I × ℕ × ℕ),
          (acc (r.2.1 + out.2.1) (r.2.2 + out.2.2) : ℝ≥0∞)
            = (acc r.2.1 r.2.2 : ℝ≥0∞) + (acc out.2.1 out.2.2 : ℝ≥0∞) := by
        intro r out
        rw [hacc, Nat.cast_add]
      have hidx : (off + 1) + 1 = off + 2 := by omega
      rw [runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
      rw [tick, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      simp only [sourceNext]
      rw [sourceTransition, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      have hsplit : ∀ out : Option I × ℕ × ℕ,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((runFor (sourceNext A hA j₀ S) N)
              (if out.1.isSome then Sum.inl (out.1, c1 + out.2.1, c2 + out.2.2)
               else Sum.inr (off + 2, c1 + out.2.1, c2 + out.2.2)))
              (fun x => (sourceAccumulated acc x.1 : ℝ≥0∞))
            = (acc (c1 + out.2.1) (c2 + out.2.2) : ℝ≥0∞)
              + (if out.1 = none then
                  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                    (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) N (off + 1))
                    (fun o => (acc o.2.1 o.2.2 : ℝ≥0∞))
                else 0) := by
        intro out
        rcases Option.eq_none_or_eq_some out.1 with hnone | ⟨y0, hy0⟩
        · rw [hnone, Option.isSome_none]
          rw [if_neg (by simp)]
          rw [← hidx]
          rw [ih (off + 1) (c1 + out.2.1) (c2 + out.2.2)]
          rw [if_pos rfl]
        · rw [hy0, Option.isSome_some]
          rw [if_pos (by simp), runFor_halted,
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
          simp only [sourceAccumulated]
          rw [if_neg (by simp)]
          simp
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
      have hsplit2 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off + 1))
          (fun a => (acc (c1 + a.2.1) (c2 + a.2.2) : ℝ≥0∞))
        = (acc c1 c2 : ℝ≥0∞)
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off + 1))
            (fun a => (acc a.2.1 a.2.2 : ℝ≥0∞)) := by
        have hpoint : ∀ a : Option I × ℕ × ℕ,
            (acc (c1 + a.2.1) (c2 + a.2.2) : ℝ≥0∞)
              = (acc c1 c2 : ℝ≥0∞) + (acc a.2.1 a.2.2 : ℝ≥0∞) := by
          intro a
          rw [hacc, Nat.cast_add]
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hpoint, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
      rw [hsplit2]
      rw [expectation_indicator_mul']
      rw [windowLoop_ledger_expectation_succ A hA j₀ S (sourceQSearchRound A hA j₀ S)
        (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)) hL N off]
      ring
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
