/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
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

/-!
# Source and shifted quantum-search rounds

This module defines randomized search rounds with an initial direct preparation trial and a
uniformly sampled amplitude-amplification depth after failure. `sourceQSearchRound` samples
depths 1 through M, while `shiftedQSearchRound` samples depths 0 through M − 1, where M is the
geometric search window. The construction uses the search framework of [BrassardEtAl2002].

`sourceWindowAverage` and `shiftedWindowAverage` describe the corresponding success averages.
Their difference is an explicit boundary term, which also gives the exact difference between the
two round success probabilities.

## Main statements

* `depthSuccessMass_eq_sin`: the success probability after a fixed amplification depth.
* `sourceWindowAverage_sub_shiftedWindowAverage`: the boundary correction between depth windows.
* `sourceRound_successMass` and `shiftedRound_successMass`: real-valued round success formulas.
* `shiftedRound_eq_frozenRound`: identification with the existing BHMT search round.

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

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
set_option warningAsError false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The source amplification depth associated with index i in a window of size M, namely i + 1. -/
def sourceDepth (M : ℕ) (i : Fin M) : ℕ := i.val + 1

/-- Every source depth in a window of size M is at most M. -/
theorem sourceDepth_lt (M : ℕ) (i : Fin M) : sourceDepth M i ≤ M := by
  have hi := i.isLt
  simp only [sourceDepth]
  omega

/-- Distinct indices in a source window give distinct amplification depths. -/
theorem sourceDepth_injective (M : ℕ) : Function.Injective (sourceDepth M) := by
  intro i j hij
  have hv : i.val = j.val := by
    simp only [sourceDepth] at hij
    omega
  exact Fin.ext hv

/-- The marked-set measurement probability after running the prepared amplitude-amplification
circuit at depth k from the basis state indexed by j₀. -/
noncomputable def depthSuccessMass (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ) : ℝ :=
  MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S

/-- The average of the depth-success masses at depths 0 through M − 1, expressed as the finite
sum divided by M. -/
noncomputable def shiftedWindowAverage (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) : ℝ :=
  (∑ i : Fin M, depthSuccessMass A j₀ S i.val) / (M : ℝ)

/-- The average of the depth-success masses at source depths 1 through M, expressed as the
finite sum divided by M. -/
noncomputable def sourceWindowAverage (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) : ℝ :=
  (∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i)) / (M : ℝ)

/-- Summing a real sequence over source depths replaces the depth-zero term of the shifted
window sum by the depth-M term. -/
theorem sum_sourceDepth_eq (p : ℕ → ℝ) (M : ℕ) :
    (∑ i : Fin M, p (sourceDepth M i)) = (∑ i : Fin M, p i.val) + p M - p 0 := by
  have hL : (∑ i : Fin M, p (sourceDepth M i)) = ∑ k ∈ Finset.range M, p (k + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    simp only [dif_pos hk']
    rfl
  have hR : (∑ i : Fin M, p i.val) = ∑ k ∈ Finset.range M, p k := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    simp only [dif_pos hk']
  have hs : (∑ k ∈ Finset.range M, p (k + 1)) = ∑ k ∈ Finset.range (M + 1), p k - p 0 := by
    have h := Finset.sum_range_succ' p M
    linarith
  have hs' : (∑ k ∈ Finset.range (M + 1), p k) = ∑ k ∈ Finset.range M, p k + p M := by
    simpa using! (Finset.sum_range_succ p M)
  rw [hL, hR, hs, hs']

/-- Adding the depth-zero term to the source-depth sum gives the sum over all depths from zero
through M. -/
theorem sum_source_eq_sum_shifted_succ (p : ℕ → ℝ) (M : ℕ) :
    (∑ i : Fin M, p (sourceDepth M i)) + p 0 = ∑ i : Fin (M + 1), p i.val := by
  have hL : (∑ i : Fin M, p (sourceDepth M i)) = ∑ k ∈ Finset.range M, p (k + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    simp only [dif_pos hk']
    rfl
  have hR : (∑ i : Fin (M + 1), p i.val) = ∑ k ∈ Finset.range (M + 1), p k := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M + 1 := Finset.mem_range.mp hk
    simp only [dif_pos hk']
  have hss := Finset.sum_range_succ' p M
  linarith

/-- For positive M, the source-window average equals the shifted-window average plus the depth-M
minus depth-zero success mass divided by M. -/
theorem sourceWindowAverage_eq_shifted (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    sourceWindowAverage A j₀ S M =
      shiftedWindowAverage A j₀ S M
        + (depthSuccessMass A j₀ S M - depthSuccessMass A j₀ S 0) / (M : ℝ) := by
  have h := sum_sourceDepth_eq (depthSuccessMass A j₀ S) M
  simp only [sourceWindowAverage, shiftedWindowAverage]
  rw [h]
  simp only [sub_div, add_div]
  ring

/-- For positive M, the difference of the source and shifted averages is exactly the difference
of their endpoint success masses divided by M. -/
theorem sourceWindowAverage_sub_shiftedWindowAverage (A : Matrix I I ℂ) (j₀ : I)
    (S : Finset I) (M : ℕ) (hM : 0 < M) :
    sourceWindowAverage A j₀ S M - shiftedWindowAverage A j₀ S M
      = (depthSuccessMass A j₀ S M - depthSuccessMass A j₀ S 0) / (M : ℝ) := by
  have h := sourceWindowAverage_eq_shifted A j₀ S M hM
  linarith

/-- For a positive window, the source and shifted averages differ whenever the depth-M and
depth-zero success masses differ. -/
theorem sourceWindowAverage_ne_shifted_of_boundary (A : Matrix I I ℂ) (j₀ : I)
    (S : Finset I) (M : ℕ) (hM : 0 < M)
    (hbound : depthSuccessMass A j₀ S M ≠ depthSuccessMass A j₀ S 0) :
    sourceWindowAverage A j₀ S M ≠ shiftedWindowAverage A j₀ S M := by
  intro h
  have hd := sourceWindowAverage_sub_shiftedWindowAverage A j₀ S M hM
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hz : depthSuccessMass A j₀ S M - depthSuccessMass A j₀ S 0 = 0 := by
    have hdiv : (depthSuccessMass A j₀ S M - depthSuccessMass A j₀ S 0) / (M : ℝ) = 0 := by
      rw [← hd, h]
      ring
    field_simp at hdiv
    linarith
  have hne : depthSuccessMass A j₀ S M = depthSuccessMass A j₀ S 0 := by linarith
  exact hbound hne

/-- For unitary preparation with initial marked probability sin² θ and 0 < θ < π/2, success
after k amplification steps is sin²((2k + 1)θ) [BrassardEtAl2002]. -/
theorem depthSuccessMass_eq_sin (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ)
    (k : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    depthSuccessMass A j₀ S k = (Real.sin ((2 * (k : ℝ) + 1) * θ))^2 := by
  exact prepared_aa_born_success A j₀ S θ k hA hθ0 hθ1 hprob

/-- Under the stated unitary and amplitude-angle hypotheses, the sum of success masses at depths
0 through M − 1 is M/2 − sin(4Mθ)/(4 sin(2θ)) for positive M. -/
theorem shiftedWindowSum_closed (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (M : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 0 < M)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    (∑ i : Fin M, depthSuccessMass A j₀ S i.val)
      = (M : ℝ) * (1 / 2
          - Real.sin (4 * (M : ℝ) * θ) / (4 * (M : ℝ) * Real.sin (2 * θ))) := by
  have hu := prepared_aa_uniform_window A j₀ S θ M hA hM hθ0 hθ1 hprob
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hconv : (∑ i : Fin M, MeasureProb
        (Run (preparedMark S) (preparedAACircuit A j₀ i.val) (Qatlib.Foundations.PureStateMath.Ket j₀)) S)
      = ∑ i : Fin M, depthSuccessMass A j₀ S i.val := by
    rfl
  rw [hconv] at hu
  rw [div_eq_iff hM'] at hu
  linarith

/-- Under the stated unitary and amplitude-angle hypotheses, the success sum at depths 1 through
M is the corresponding sum through depth M starting at zero, minus sin² θ, with the
displayed trigonometric closed form. -/
theorem sourceWindowSum_closed (A : Matrix I I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (M : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 0 < M)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    (∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i))
      = ((M + 1 : ℕ) : ℝ) * (1 / 2
          - Real.sin (4 * ((M + 1 : ℕ) : ℝ) * θ)
            / (4 * ((M + 1 : ℕ) : ℝ) * Real.sin (2 * θ))) - (Real.sin θ)^2 := by
  have hM1 : 0 < M + 1 := by omega
  have hbig := shiftedWindowSum_closed A j₀ S θ (M + 1) hA hM1 hθ0 hθ1 hprob
  have hsum := sum_source_eq_sum_shifted_succ (depthSuccessMass A j₀ S) M
  have hconv : (∑ i : Fin (M + 1), (Real.sin ((2 * (i.val : ℝ) + 1) * θ))^2)
      = ∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (depthSuccessMass_eq_sin A j₀ S θ i.val hA hθ0 hθ1 hprob).symm
  have hz : depthSuccessMass A j₀ S 0 = (Real.sin θ)^2 := by
    have := depthSuccessMass_eq_sin A j₀ S θ 0 hA hθ0 hθ1 hprob
    simpa using! this
  calc
    (∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i))
        = ∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val
            - depthSuccessMass A j₀ S 0 := by linarith [hsum]
    _ = (∑ i : Fin (M + 1), (Real.sin ((2 * (i.val : ℝ) + 1) * θ))^2)
            - depthSuccessMass A j₀ S 0 := by rw [hconv]
    _ = ((M + 1 : ℕ) : ℝ) * (1 / 2
          - Real.sin (4 * ((M + 1 : ℕ) : ℝ) * θ)
            / (4 * ((M + 1 : ℕ) : ℝ) * Real.sin (2 * θ))) - (Real.sin θ)^2 := by
        rw [hconv, hbig, hz]

/-- Every geometric quantum-search window has positive size. -/
theorem qSearchWindow_pos (l : ℕ) : 0 < qSearchWindow l := by
  have h : 1 ≤ qSearchWindow l := Nat.le_max_left _ _
  omega

/-- Performs a direct preparation trial and, on failure, a uniformly selected trial from the
supplied window. It returns only marked outcomes, with costs (1, 1) for direct success and
the supplied window ledger otherwise. -/
noncomputable def windowRound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ))
    (ledger : Fin M → ℕ × ℕ) : PMF (Option I × ℕ × ℕ) :=
  PMF.bind (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1)) fun st =>
    if st.1.1 ∈ S then
      PMF.pure (some st.1.1, 1, 1)
    else
      PMF.bind
        (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩) fun j =>
        PMF.bind (trial j) fun st2 =>
          PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
            (ledger j).1, (ledger j).2)

/-- A search round whose fallback trial samples depths 1 through the geometric window size M
uniformly, recording fallback costs (2 + 2k, 2 + k) at depth k. -/
noncomputable def sourceQSearchRound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (l : ℕ) : PMF (Option I × ℕ × ℕ) :=
  windowRound A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    (fun j => preparedAATrial A hA j₀ S
      (⟨sourceDepth (qSearchWindow l) j, by omega⟩
        : Fin (sourceDepth (qSearchWindow l) j + 1)))
    (fun j => (2 + 2 * sourceDepth (qSearchWindow l) j, 2 + sourceDepth (qSearchWindow l) j))

/-- A search round whose fallback trial samples depths 0 through M − 1 uniformly for the
geometric window size M, recording fallback costs (2 + 2k, 2 + k) at depth k. -/
noncomputable def shiftedQSearchRound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (l : ℕ) : PMF (Option I × ℕ × ℕ) :=
  windowRound A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    (fun j => preparedAATrial A hA j₀ S j)
    (fun j => (2 + 2 * j.val, 2 + j.val))

/-- The expectation of a constant c on an event and zero elsewhere equals c times the event mass
in the extended nonnegative reals. -/
theorem expectation_indicator_mul' {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] (c : ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun a => if P a then c else 0) = c * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq p P,
      ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      (fun a => by by_cases hP : P a <;> simp [hP])

/-- The direct preparation trial returns a marked index with mass equal to the initial marked
measurement probability, cast to the extended nonnegative reals. -/
theorem directABranch_mass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        (fun x => x.1.1 ∈ S)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  rw [(prepared_aa_trial_actual_metadata A j₀ S hA (⟨0, Nat.zero_lt_one⟩ : Fin 1)).2.2,
    show ((⟨0, Nat.zero_lt_one⟩ : Fin 1) : ℕ) = 0 from rfl,
    (prepared_aa_actual_circuit A j₀ S 0 hA).2.2.2, pow_zero, applyGate_one]

/-- The unmarked-event mass of the direct preparation trial is one minus its initial marked
measurement probability. -/
theorem directABranch_compl (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        (fun x => ¬ x.1.1 ∈ S)
      = 1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  have hpair := event_compl (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
    (fun x => x.1.1 ∈ S)
  rw [directABranch_mass] at hpair
  rw [add_comm] at hpair
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hpair

/-- The uniform distribution on `Fin m` assigns each index mass 1/m when m is positive. -/
private theorem uniform_apply_univ' {m : ℕ} (hm : 0 < m)
    (hs : (Finset.univ : Finset (Fin m)).Nonempty) (j : Fin m) :
    PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hs j = ((m : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [PMF.uniformOfFinset_apply, if_pos (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- If each trial's marked-event mass equals its specified depth-success mass, averaging over
the uniform window gives the sum of these masses divided by the window size. -/
private theorem uniform_trial_event {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ)) (depth : Fin M → ℕ)
    (htrial : ∀ j, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S)
        = ENNReal.ofReal (depthSuccessMass A j₀ S (depth j))) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩)
        (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S))
      = ((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
          (depthSuccessMass A j₀ S (depth j)) := by
  have hexp : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩)
        (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S))
    = ∑' j, (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩) j *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S) := rfl
  rw [hexp, tsum_fintype, Finset.sum_congr rfl (fun j _ => by
    rw [uniform_apply_univ' hM ⟨⟨0, hM⟩, Finset.mem_univ _⟩ j]),
    ← Finset.mul_sum, Finset.sum_congr rfl (fun j _ => htrial j)]

/-- The success-event mass of a window round is the initial marked mass plus its complement
times the uniform average of the fallback depth-success masses, under the stated trial-mass
identities. -/
theorem windowRound_success_mass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ)) (ledger : Fin M → ℕ × ℕ)
    (depth : Fin M → ℕ)
    (htrial : ∀ j, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S)
        = ENNReal.ofReal (depthSuccessMass A j₀ S (depth j))) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowRound A hA j₀ S M hM trial ledger) (fun out => ∃ y, out.1 = some y)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) *
          (((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
            (depthSuccessMass A j₀ S (depth j))) := by
  rw [windowRound]
  have houter : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (PMF.bind (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        (fun st => if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
          else PMF.bind
            (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
              ⟨⟨0, hM⟩, Finset.mem_univ _⟩) fun j =>
            PMF.bind (trial j) fun st2 =>
              PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                (ledger j).1, (ledger j).2)))
        (fun out => ∃ y, out.1 = some y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
          (fun st => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
              else PMF.bind
                (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
                  ⟨⟨0, hM⟩, Finset.mem_univ _⟩) fun j =>
                PMF.bind (trial j) fun st2 =>
                  PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                    (ledger j).1, (ledger j).2))
            (fun out => ∃ y, out.1 = some y)) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
        (fun out => (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq _ _).symm)
  have hsplit : ∀ st : (I × ℕ) × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
          else PMF.bind
            (PMF.uniformOfFinset (Finset.univ : Finset (Fin M))
              ⟨⟨0, hM⟩, Finset.mem_univ _⟩) fun j =>
            PMF.bind (trial j) fun st2 =>
              PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                (ledger j).1, (ledger j).2))
        (fun out => ∃ y, out.1 = some y)
      = if st.1.1 ∈ S then (1:ℝ≥0∞) else
          (((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
            (depthSuccessMass A j₀ S (depth j))) := by
    intro st
    by_cases hS : st.1.1 ∈ S
    · rw [if_pos hS, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      rw [if_pos ⟨st.1.1, rfl⟩, if_pos hS]
    · rw [if_neg hS]
      have inner : ∀ j : Fin M,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
              (PMF.bind (trial j) fun st2 =>
                PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                  (ledger j).1, (ledger j).2))
              (fun out => ∃ y, out.1 = some y)
            = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S) := by
        intro j
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
        refine Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
            (fun a => ?_)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
        by_cases h2 : a.1.1 ∈ S <;> simp [h2]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr (fun j => (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq _ _).symm),
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr inner,
        uniform_trial_event A hA j₀ S M hM trial depth htrial, if_neg hS]
  rw [houter, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit]
  have hfun : ∀ st : (I × ℕ) × ℕ,
      (if st.1.1 ∈ S then (1:ℝ≥0∞)
          else (((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
            (depthSuccessMass A j₀ S (depth j))))
        = (if st.1.1 ∈ S then (1:ℝ≥0∞) else 0)
          + (if ¬ (st.1.1 ∈ S) then
              (((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
                (depthSuccessMass A j₀ S (depth j)))
            else 0) := by
    intro st; by_cases hS : st.1.1 ∈ S <;> simp [hS]
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hfun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    expectation_indicator_mul', expectation_indicator_mul',
    directABranch_mass, directABranch_compl]
  ring

/-- The source round's success-event mass is the initial marked mass plus its complement times
the average fallback success mass over depths 1 through the search-window size. -/
theorem sourceRound_success_mass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) *
          (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (depthSuccessMass A j₀ S (sourceDepth (qSearchWindow l) j))) := by
  refine windowRound_success_mass A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    _ _ (sourceDepth (qSearchWindow l)) ?_
  intro j
  exact (prepared_aa_trial_actual_metadata A j₀ S hA
    (⟨sourceDepth (qSearchWindow l) j, by omega⟩
      : Fin (sourceDepth (qSearchWindow l) j + 1))).2.2

/-- The shifted round's success-event mass is the initial marked mass plus its complement times
the average fallback success mass over depths zero through one less than the search-window
size. -/
theorem shiftedRound_success_mass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (shiftedQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) *
          (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (depthSuccessMass A j₀ S j.val)) := by
  refine windowRound_success_mass A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    _ _ (fun j => j.val) ?_
  intro j
  exact (prepared_aa_trial_actual_metadata A j₀ S hA j).2.2

/-- The shifted search-round distribution equals the existing `BHMTQSearch.qSearchRound`
distribution. -/
theorem shiftedRound_eq_frozenRound (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    shiftedQSearchRound A hA j₀ S l = BHMTQSearch.qSearchRound A hA j₀ S l := by
  unfold shiftedQSearchRound windowRound BHMTQSearch.qSearchRound
  apply PMF.ext
  intro x
  simp only [PMF.bind_apply]

/-- The marked measurement mass after any prepared amplification depth is nonnegative. -/
theorem depthSuccessMass_nonneg (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ) :
    0 ≤ depthSuccessMass A j₀ S k :=
  measureProb_nonneg _ _

/-- The real-valued mass of the event that a round's optional index is present. -/
noncomputable def roundSuccessMass {I : Type} (p : PMF (Option I × ℕ × ℕ)) : ℝ :=
  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun out => ∃ y, out.1 = some y)).toReal

/-- Under the stated trial-mass identities, a window round's real success mass is a + (1 − a) ·
w, where a is the initial marked probability and w is the average fallback depth-success
mass. -/
theorem windowRound_successMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ)) (ledger : Fin M → ℕ × ℕ)
    (depth : Fin M → ℕ)
    (htrial : ∀ j, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (trial j) (fun x => x.1.1 ∈ S)
        = ENNReal.ofReal (depthSuccessMass A j₀ S (depth j))) :
    roundSuccessMass (windowRound A hA j₀ S M hM trial ledger)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * ((∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) / (M : ℝ)) := by
  have h := windowRound_success_mass A hA j₀ S M hM trial ledger depth htrial
  have ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S := measureProb_nonneg _ _
  have ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hnonneg : ∀ j, 0 ≤ depthSuccessMass A j₀ S (depth j) :=
    fun j => depthSuccessMass_nonneg A j₀ S (depth j)
  have hsum : (∑ j : Fin M, ENNReal.ofReal (depthSuccessMass A j₀ S (depth j)))
      = ENNReal.ofReal (∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) :=
    (ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg j)).symm
  have hinv : ((M : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (M : ℝ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < (M:ℝ))]
    congr 1
    field_simp
  have hone : (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S))
      = ENNReal.ofReal (1 - MeasureProb (preparedAAState A j₀) S) := by
    rw [ENNReal.ofReal_sub 1 (by linarith [ha1]), ENNReal.ofReal_one]
  have hsumpos : (0:ℝ) ≤ ∑ j : Fin M, depthSuccessMass A j₀ S (depth j) :=
    Finset.sum_nonneg fun j _ => hnonneg j
  have hone1 : (0:ℝ) ≤ 1 - MeasureProb (preparedAAState A j₀) S := by linarith [ha1]
  have hinvpos : (0:ℝ) ≤ 1 / (M : ℝ) := by positivity
  have hprod : (0:ℝ) ≤ (1 / (M : ℝ))
      * (∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) :=
    mul_nonneg hinvpos hsumpos
  have hone2 : (0:ℝ) ≤ (1 - MeasureProb (preparedAAState A j₀) S)
      * ((1 / (M : ℝ)) * (∑ j : Fin M, depthSuccessMass A j₀ S (depth j))) :=
    mul_nonneg hone1 hprod
  have hENN : ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) *
          (((M : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ENNReal.ofReal
            (depthSuccessMass A j₀ S (depth j)))
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S
          + (1 - MeasureProb (preparedAAState A j₀) S)
            * ((∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) / (M : ℝ))) := by
    rw [hone, hsum, hinv]
    rw [← ENNReal.ofReal_mul hinvpos]
    rw [← ENNReal.ofReal_mul hone1]
    rw [← ENNReal.ofReal_add ha0 hone2]
    congr 1
    field_simp
  simp only [roundSuccessMass]
  rw [h, hENN]
  have hquot : (0:ℝ) ≤ (∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) / (M : ℝ) := by
    exact div_nonneg hsumpos (by positivity)
  have hpos : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S
      + (1 - MeasureProb (preparedAAState A j₀) S)
        * ((∑ j : Fin M, depthSuccessMass A j₀ S (depth j)) / (M : ℝ)) := by
    exact add_nonneg ha0 (mul_nonneg hone1 hquot)
  rw [ENNReal.toReal_ofReal hpos]

/-- The source round's real success mass is a + (1 − a) · w, where a is the initial marked
probability and w is `sourceWindowAverage` at the geometric window size. -/
theorem sourceRound_successMass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * sourceWindowAverage A j₀ S (qSearchWindow l) := by
  refine windowRound_successMass A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    _ _ (sourceDepth (qSearchWindow l)) ?_
  intro j
  exact (prepared_aa_trial_actual_metadata A j₀ S hA
    (⟨sourceDepth (qSearchWindow l) j, by omega⟩
      : Fin (sourceDepth (qSearchWindow l) j + 1))).2.2

/-- The shifted round's real success mass is a + (1 − a) · w, where a is the initial marked
probability and w is `shiftedWindowAverage` at the geometric window size. -/
theorem shiftedRound_successMass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (shiftedQSearchRound A hA j₀ S l)
      = MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S)
          * shiftedWindowAverage A j₀ S (qSearchWindow l) := by
  refine windowRound_successMass A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l)
    _ _ (fun j => j.val) ?_
  intro j
  exact (prepared_aa_trial_actual_metadata A j₀ S hA j).2.2

/-- The source-minus-shifted round success mass equals (1 − a) times the depth-M minus
depth-zero success mass divided by M, where a is the initial marked probability and M is the
search-window size. -/
theorem sourceRound_successMass_sub_shiftedRound (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      - roundSuccessMass (shiftedQSearchRound A hA j₀ S l)
      = (1 - MeasureProb (preparedAAState A j₀) S)
        * ((depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
            / (qSearchWindow l : ℝ)) := by
  have hs := sourceRound_successMass A hA j₀ S l
  have ht := shiftedRound_successMass A hA j₀ S l
  have hwin := sourceWindowAverage_eq_shifted A j₀ S (qSearchWindow l)
    (qSearchWindow_pos l)
  rw [hs, ht, hwin]
  ring

/-- The source and shifted round success masses differ when their endpoint depth-success masses
differ and the initial marked probability is not one. -/
theorem sourceRound_successMass_ne_shiftedRound_of_boundary (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ)
    (hbound : depthSuccessMass A j₀ S (qSearchWindow l) ≠ depthSuccessMass A j₀ S 0)
    (hA1 : MeasureProb (preparedAAState A j₀) S ≠ 1) :
    roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      ≠ roundSuccessMass (shiftedQSearchRound A hA j₀ S l) := by
  intro h
  have hs := sourceRound_successMass A hA j₀ S l
  have ht := shiftedRound_successMass A hA j₀ S l
  have hprod : (1 - MeasureProb (preparedAAState A j₀) S) *
      (sourceWindowAverage A j₀ S (qSearchWindow l)
        - shiftedWindowAverage A j₀ S (qSearchWindow l)) = 0 := by
    rw [hs, ht] at h
    calc
      (1 - MeasureProb (preparedAAState A j₀) S) *
          (sourceWindowAverage A j₀ S (qSearchWindow l)
            - shiftedWindowAverage A j₀ S (qSearchWindow l))
          = (MeasureProb (preparedAAState A j₀) S
              + (1 - MeasureProb (preparedAAState A j₀) S)
                * sourceWindowAverage A j₀ S (qSearchWindow l))
            - (MeasureProb (preparedAAState A j₀) S
              + (1 - MeasureProb (preparedAAState A j₀) S)
                * shiftedWindowAverage A j₀ S (qSearchWindow l)) := by ring
      _ = 0 := sub_eq_zero.mpr h
  rw [mul_eq_zero] at hprod
  rcases hprod with h1 | h2
  · have hcon : MeasureProb (preparedAAState A j₀) S = 1 := by linarith
    exact hA1 hcon
  · exact (sourceWindowAverage_ne_shifted_of_boundary A j₀ S (qSearchWindow l)
      (qSearchWindow_pos l) hbound) (sub_eq_zero.mp h2)
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
