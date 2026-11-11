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
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch

/-!
# Expected costs of source quantum search

This module bounds the two cost ledgers of `sourceQSearchRound` and `sourceQSearchLoop` for the
geometric search schedule. It uses the amplitude-amplification framework of [BrassardEtAl2002],
with source depths starting at one, to control mature-round failure and sum the expected costs
of all reached rounds.

`sourceStopLedgerExpectation` expresses the resulting infinite cost series. Finite execution
expectations converge to this series, and each ledger is bounded by 400 / √a when the initial
marked probability a is positive.

## Main statements

* `sourceRound_fail_prob_le_three_quarters`: a mature source round fails with probability at
  most 3/4.
* `sourceQSearchLoop_ledger_expectation_unfold`: additive ledger expectations decompose over
  reached rounds.
* `sourceLoop_ledger1_expectation_le` and `sourceLoop_ledger2_expectation_le`: uniform bounds
  for finite horizons.
* `sourceStopLedgerExpectation_le`: the two bounds extend to the infinite cost series.

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

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
set_option warningAsError false

/-- For M ≥ 1 and u ≥ 0, the product (1 − u)(3M − 1 + 4u) is at most 3M. -/
private lemma source_failure_bound (u M : ℝ) (hM1 : 1 ≤ M) (hu0 : 0 ≤ u) :
    (1 - u) * (3 * M - 1 + 4 * u) ≤ 3 * M := by
  have hMu : 1 * u ≤ M * u := mul_le_mul_of_nonneg_right hM1 hu0
  have hsq : 0 ≤ (2 * u - 1 / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- A source search round has failure probability at most 3/4 when its window satisfies (M + 1)
sin(2θ) ≥ 1 and the initial marked probability is sin² θ with 0 < θ < π/2. -/
theorem sourceRound_fail_prob_le_three_quarters {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) * Real.sin (2 * θ)) :
    1 - roundSuccessMass (sourceQSearchRound A hA j₀ S l) ≤ 3 / 4 := by
  set M := qSearchWindow l with hMdef
  have hMpos : 0 < M := qSearchWindow_pos l
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ qSearchWindow l := Nat.le_max_left _ _
    simpa [hMdef] using! h1
  have hM1R : 1 ≤ (M : ℝ) := by
    rw [← Nat.cast_one]
    exact (Nat.cast_le).2 hM1
  have hMR : (0:ℝ) < (M : ℝ) := by
    rw [← Nat.cast_zero]
    exact (Nat.cast_lt).2 hMpos
  have hu0 : 0 ≤ (Real.sin θ)^2 := sq_nonneg _
  have hu1 : (Real.sin θ)^2 ≤ 1 := by
    have habs := Real.abs_sin_le_one θ
    have habs0 : 0 ≤ |Real.sin θ| := abs_nonneg _
    rw [← sq_abs]
    nlinarith
  set S0 : ℝ := ((M + 1 : ℕ) : ℝ) / 4 - (Real.sin θ)^2 with hS0def
  have hdepth : ∀ d : ℕ, depthSuccessMass A j₀ S d = (Real.sin ((2*(d:ℝ)+1)*θ))^2 := by
    intro d
    rw [depthSuccessMass, prepared_aa_born_success A j₀ S θ d hA hθ0 hθ1 hprob]
  have hmature' : 1 ≤ ((M + 1 : ℕ) : ℝ) * Real.sin (2 * θ) := by
    simpa [hMdef] using! hmature
  have hq : 1 / 4 ≤ (∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val)
      / ((M + 1 : ℕ) : ℝ) := by
    have h := prepared_aa_uniform_success_lower A j₀ S θ (M + 1) hA (by omega) hθ0 hθ1
      hprob hmature'
    simpa only [depthSuccessMass] using! h
  have hq' : ((M + 1 : ℕ) : ℝ) / 4
      ≤ ∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val := by
    have hD : (0:ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    have h := (le_div_iff₀ hD).mp hq
    calc ((M + 1 : ℕ) : ℝ) / 4 = (1 / 4 : ℝ) * ((M + 1 : ℕ) : ℝ) := by ring
      _ ≤ ∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val := h
  have hsum : (∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i))
      = (∑ i : Fin (M + 1), depthSuccessMass A j₀ S i.val) - depthSuccessMass A j₀ S 0 := by
    have h := sum_source_eq_sum_shifted_succ (depthSuccessMass A j₀ S) M
    linarith
  have hsumlb : S0
      ≤ ∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i) := by
    have h0 : depthSuccessMass A j₀ S 0 = (Real.sin θ)^2 := by
      simpa using! hdepth 0
    rw [hS0def]
    linarith [hsum, hq']
  have havg : sourceWindowAverage A j₀ S M ≥ S0 / (M : ℝ) := by
    simp only [sourceWindowAverage]
    have h1 : S0 / (M : ℝ)
        ≤ (∑ i : Fin M, depthSuccessMass A j₀ S (sourceDepth M i)) / (M : ℝ) := by
      rw [le_div_iff₀ hMR]
      have hone : S0 / (M : ℝ) * (M : ℝ) = S0 := by
        field_simp
      rw [hone]
      exact hsumlb
    exact h1
  have hsucc' : roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      = (Real.sin θ)^2 + (1 - (Real.sin θ)^2) * sourceWindowAverage A j₀ S M := by
    rw [sourceRound_successMass A hA j₀ S l]
    simp only [hprob]
    rfl
  have hfail : 1 - roundSuccessMass (sourceQSearchRound A hA j₀ S l)
      = (1 - (Real.sin θ)^2) * (1 - sourceWindowAverage A j₀ S M) := by
    rw [hsucc']
    ring
  have hnonneg : 0 ≤ 1 - (Real.sin θ)^2 := by linarith
  have hmain : (1 - (Real.sin θ)^2) * (1 - sourceWindowAverage A j₀ S M)
      ≤ (1 - (Real.sin θ)^2) * (1 - S0 / (M : ℝ)) := by
    have hle : S0 / (M : ℝ) ≤ sourceWindowAverage A j₀ S M := havg
    have hle' : 1 - sourceWindowAverage A j₀ S M ≤ 1 - S0 / (M : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_left hle' hnonneg
  have hfinal : (1 - (Real.sin θ)^2) * (1 - S0 / (M : ℝ)) ≤ 3 / 4 := by
    have hident : 1 - S0 / (M : ℝ)
        = (3 * (M : ℝ) - 1 + 4 * (Real.sin θ)^2) / (4 * (M : ℝ)) := by
      rw [hS0def]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      field_simp
      ring
    rw [hident]
    have hone : (1 - (Real.sin θ)^2) * ((3 * (M : ℝ) - 1 + 4 * (Real.sin θ)^2)
          / (4 * (M : ℝ)))
        = ((1 - (Real.sin θ)^2) * (3 * (M : ℝ) - 1 + 4 * (Real.sin θ)^2))
          / (4 * (M : ℝ)) := by ring
    rw [hone]
    have h4M : (0:ℝ) < 4 * (M : ℝ) := by positivity
    rw [div_le_iff₀ h4M]
    have hcore : (1 - (Real.sin θ)^2) * (3 * (M : ℝ) - 1 + 4 * (Real.sin θ)^2)
        ≤ 3 * (M : ℝ) := source_failure_bound ((Real.sin θ)^2) ((M : ℝ)) hM1R hu0
    nlinarith [hcore]
  linarith [hfail, hmain, hfinal]

/-- The expected value of an additive ledger for a finite source loop is the sum of the round
ledger expectations weighted by their reach probabilities, provided the ledger vanishes at
the empty outcome. -/
theorem sourceQSearchLoop_ledger_expectation_unfold {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0) :
    ∀ T,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) L
        = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1)) L := by
  intro T
  simp only [sourceQSearchLoop]
  refine (windowLoop_ledger_expectation_unfold A hA j₀ S (sourceQSearchRound A hA j₀ S)
    L hL hL0 (sourceFailMass A hA j₀ S) (fun _ => rfl) T 0).trans ?_
  simp only [Nat.zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hidx : (1 + i) = (i + 1) := by omega
  rw [hidx]
  rfl

/-- For an additive accumulator that vanishes at zero, finite execution and the truncated source
loop have equal expected accumulated ledger values. -/
theorem sourceRunFor_ledger_eq_sourceLoop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (acc : ℕ → ℕ → ℕ)
    (hacc : ∀ a b c d : ℕ, acc (a + c) (b + d) = acc a b + acc c d)
    (hacc0 : acc 0 0 = 0) (N : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N (sourceInitial (I := I)))
        (fun x => (sourceAccumulated acc x.1 : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S N 0)
        (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)) := by
  have hb := sourceRunFor_ledger_eq_loop A hA j₀ S acc hacc hacc0 N 0 0 0
  simp only [Nat.zero_add] at hb
  simp only [sourceInitial]
  rw [hb]
  simp only [sourceQSearchLoop]
  simp [hacc0]

/-- The infinite sum of source-round ledger expectations weighted by the probability of reaching
each round, with values in the extended nonnegative reals. -/
noncomputable def sourceStopLedgerExpectation {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, sourceReachMass A hA j₀ S i
    * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1)) L

/-- Expected accumulated ledger values of finite executions converge to
`sourceStopLedgerExpectation` for an additive accumulator that vanishes at zero. -/
theorem sourceStopLedgerExpectation_eq_limit {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (acc : ℕ → ℕ → ℕ)
    (hacc : ∀ a b c d : ℕ, acc (a + c) (b + d) = acc a b + acc c d)
    (hacc0 : acc 0 0 = 0) :
    Tendsto (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
        (sourceInitial (I := I)))
        (fun x => (sourceAccumulated acc x.1 : ℝ≥0∞)))
      atTop (𝓝 (sourceStopLedgerExpectation A hA j₀ S
        (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)))) := by
  have hL : ∀ (r out : Option I × ℕ × ℕ),
      (acc (r.2.1 + out.2.1) (r.2.2 + out.2.2) : ℝ≥0∞)
        = (acc r.2.1 r.2.2 : ℝ≥0∞) + (acc out.2.1 out.2.2 : ℝ≥0∞) := by
    intro r out
    rw [hacc, Nat.cast_add]
  have hL0 : (acc 0 0 : ℝ≥0∞) = 0 := by simp [hacc0]
  have hrun : (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
        (sourceInitial (I := I)))
        (fun x => (sourceAccumulated acc x.1 : ℝ≥0∞)))
      = (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S N 0)
        (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞))) :=
    funext fun N => sourceRunFor_ledger_eq_sourceLoop A hA j₀ S acc hacc hacc0 N
  have hunfold : ∀ T,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0)
          (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞))
        = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
              (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)) :=
    sourceQSearchLoop_ledger_expectation_unfold A hA j₀ S
      (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)) hL hL0
  rw [hrun]
  rw [show (fun T => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0)
        (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)))
      = (fun n => ∑ i ∈ Finset.range n,
          sourceReachMass A hA j₀ S i
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
              (fun out => (acc out.2.1 out.2.2 : ℝ≥0∞)))
      from funext fun T => hunfold T]
  rw [← ENNReal.hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

/-- Every natural power of the real number 6/5 is at least one. -/
theorem sourceGeopow_ge_one (k : ℕ) : (1:ℝ) ≤ ((6/5:ℝ)^k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((6/5:ℝ)^k) * (6/5) := mul_le_mul ih (by norm_num) (by norm_num) (by norm_num)
        _ = (6/5:ℝ)^(k+1) := (pow_succ _ _).symm

/-- Natural powers of the real number 6/5 are monotone in the exponent. -/
theorem sourceGeopow_mono {a b : ℕ} (h : a ≤ b) : ((6/5:ℝ)^a) ≤ ((6/5:ℝ)^b) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd, pow_add]
  calc ((6/5:ℝ)^a) = ((6/5:ℝ)^a) * 1 := (mul_one _).symm
    _ ≤ ((6/5:ℝ)^a) * ((6/5:ℝ)^d) := mul_le_mul_of_nonneg_left (sourceGeopow_ge_one d)
      (by positivity)

/-- The natural-number ceiling quotient of 6^k by 5^k, multiplied by 5^k, is at least 6^k. -/
theorem sourceWindow_raw_mul (k : ℕ) : (6:ℕ)^k ≤ 5^k * ((6^k + 5^k - 1) / 5^k) := by
  have h5 : (0:ℕ) < 5^k := Nat.pow_pos (by norm_num)
  have hd := Nat.div_add_mod (6^k + 5^k - 1) (5^k)
  have hmod : (6^k + 5^k - 1) % 5^k ≤ 5^k - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ h5)
  omega

/-- The real power (6/5)^k equals the quotient of the natural powers 6^k and 5^k cast to the
reals. -/
theorem sourceWindow_pow (k : ℕ) : ((6/5:ℝ)^k) = ((6^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
  rw [div_pow]
  push_cast
  rfl

/-- The geometric search window is the natural-number quotient (6^l + 5^l − 1) / 5^l. -/
theorem sourceWindow_eq (l : ℕ) : qSearchWindow l = (6^l + 5^l - 1) / 5^l := by
  show max 1 ((6^l + 5^l - 1) / 5^l) = _
  have h5 : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
  have hge : (1:ℕ) ≤ (6^l + 5^l - 1) / 5^l := by
    rw [Nat.one_le_div_iff h5]
    have : (1:ℕ) ≤ 6^l := Nat.pow_pos (by omega)
    omega
  omega

/-- The search window at round l is at least the real geometric scale (6/5)^l. -/
theorem sourceWindow_ge (l : ℕ) : ((6/5:ℝ)^l) ≤ (qSearchWindow l : ℝ) := by
  have h5 : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
  have h5R : (0:ℝ) < ((5^l:ℕ):ℝ) := by exact_mod_cast h5
  have hceil : ((6^l:ℕ):ℝ)/((5^l:ℕ):ℝ) ≤ (((6^l + 5^l - 1)/5^l : ℕ):ℝ) := by
    rw [div_le_iff₀ h5R]
    calc ((6^l:ℕ):ℝ) ≤ ((5^l * ((6^l + 5^l - 1)/5^l) : ℕ):ℝ) := by
          push_cast
          exact_mod_cast sourceWindow_raw_mul l
      _ = (((6^l + 5^l - 1)/5^l : ℕ):ℝ) * ((5^l:ℕ):ℝ) := by push_cast; ring
  rw [sourceWindow_eq, sourceWindow_pow]
  exact hceil

/-- The search window at round l is at most twice the real geometric scale (6/5)^l. -/
theorem sourceWindow_le (l : ℕ) : (qSearchWindow l : ℝ) ≤ 2 * ((6/5:ℝ)^l) := by
  have h5R : (0:ℝ) < ((5^l:ℕ):ℝ) := by
    have : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
    exact_mod_cast this
  have hhigh : (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6/5:ℝ)^l) + 1 := by
    have h1 : (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) := Nat.cast_div_le
    have h2 : ((6^l+5^l-1:ℕ):ℝ) ≤ ((6^l+5^l:ℕ):ℝ) := by exact_mod_cast (Nat.sub_le _ _)
    have h3 : ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) ≤ ((6^l+5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : ((6^l+5^l:ℕ):ℝ) = ((6^l:ℕ):ℝ) + ((5^l:ℕ):ℝ) := Nat.cast_add _ _
    calc (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) := h1
      _ ≤ ((6^l+5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := h3
      _ = ((6^l:ℕ):ℝ)/((5^l:ℕ):ℝ) + ((5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := by rw [h4, add_div]
      _ = ((6/5:ℝ)^l) + 1 := by rw [← sourceWindow_pow, div_self (ne_of_gt h5R)]
  have hcast : (qSearchWindow l : ℝ) = (((6^l+5^l-1)/5^l : ℕ):ℝ) := by rw [sourceWindow_eq]
  rw [hcast]
  have hge := sourceGeopow_ge_one l
  linarith

/-- Every supported source-round outcome has first ledger at most 2 + 2M and second ledger at
most 2 + M, where M is the round's search window. -/
theorem sourceRound_ledger_shape {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (l : ℕ) (out : Option I × ℕ × ℕ)
    (hout : out ∈ (sourceQSearchRound A hA j₀ S l).support) :
    out.2.1 ≤ 2 + 2 * qSearchWindow l ∧ out.2.2 ≤ 2 + qSearchWindow l := by
  rw [sourceQSearchRound] at hout
  rw [windowRound] at hout
  obtain ⟨st, hst, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  by_cases hS : st.1.1 ∈ S
  · rw [if_pos hS] at hout
    have hout' : out = (some st.1.1, 1, 1) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst hout'
    have h1w : (1:ℕ) ≤ qSearchWindow l := Nat.le_max_left _ _
    constructor
    · show (1:ℕ) ≤ 2 + 2 * qSearchWindow l
      omega
    · show (1:ℕ) ≤ 2 + qSearchWindow l
      omega
  · rw [if_neg hS] at hout
    obtain ⟨j, hj, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨st2, hst2, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have hout' : out = (if st2.1.1 ∈ S then some st2.1.1 else none,
        2 + 2 * sourceDepth (qSearchWindow l) j, 2 + sourceDepth (qSearchWindow l) j) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst hout'
    have hsd : sourceDepth (qSearchWindow l) j ≤ qSearchWindow l := sourceDepth_lt _ _
    constructor
    · show (2 + 2 * sourceDepth (qSearchWindow l) j : ℕ) ≤ 2 + 2 * qSearchWindow l
      omega
    · show (2 + sourceDepth (qSearchWindow l) j : ℕ) ≤ 2 + qSearchWindow l
      omega

/-- The expected first ledger of source round l is at most 6(6/5)^l. -/
theorem sourceRound_ledger1_expectation_le (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) := by
  refine le_trans (expectation_le_of_support (sourceQSearchRound A hA j₀ S l)
    (fun out => (out.2.1 : ℝ≥0∞)) ((2 + 2 * (qSearchWindow l) : ℕ) : ℝ≥0∞) ?_) ?_
  · intro out hout
    have h := sourceRound_ledger_shape A hA j₀ S l out hout
    show ((out.2.1 : ℕ) : ℝ≥0∞) ≤ ((2 + 2 * (qSearchWindow l) : ℕ) : ℝ≥0∞)
    exact_mod_cast h.1
  · have h1 : ((2 + 2 * (qSearchWindow l) : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((2 + 2 * (qSearchWindow l) : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw := sourceWindow_le l
    have hge := sourceGeopow_ge_one l
    have hsplit : (((2 + 2 * (qSearchWindow l) : ℕ):ℝ)) = 2 + 2 * ((qSearchWindow l : ℕ):ℝ) := by
      push_cast
      ring
    rw [hsplit]
    nlinarith

/-- The expected second ledger of source round l is at most 4(6/5)^l. -/
theorem sourceRound_ledger2_expectation_le (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) := by
  refine le_trans (expectation_le_of_support (sourceQSearchRound A hA j₀ S l)
    (fun out => (out.2.2 : ℝ≥0∞)) ((2 + (qSearchWindow l) : ℕ) : ℝ≥0∞) ?_) ?_
  · intro out hout
    have h := sourceRound_ledger_shape A hA j₀ S l out hout
    show ((out.2.2 : ℕ) : ℝ≥0∞) ≤ ((2 + (qSearchWindow l) : ℕ) : ℝ≥0∞)
    exact_mod_cast h.2
  · have h1 : ((2 + (qSearchWindow l) : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((2 + (qSearchWindow l) : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw := sourceWindow_le l
    have hge := sourceGeopow_ge_one l
    have hsplit : (((2 + (qSearchWindow l) : ℕ):ℝ)) = 2 + ((qSearchWindow l : ℕ):ℝ) := by
      push_cast
      ring
    rw [hsplit]
    nlinarith

/-- The event that a source round returns `none` has mass at most 3/4 under the stated
amplitude-angle and mature-window hypotheses. -/
theorem sourceFailMass_le_three_quarters {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) * Real.sin (2 * θ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ ENNReal.ofReal (3 / 4) := by
  have hreal := sourceRound_fail_prob_le_three_quarters A hA j₀ S θ l hθ0 hθ1 hprob hmature
  have hsucc_le : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l)
      (fun out => ∃ y, out.1 = some y) ≤ 1 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
  have hsucc_ne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l)
      (fun out => ∃ y, out.1 = some y) ≠ ∞ := by
    intro h
    rw [h] at hsucc_le
    exact absurd hsucc_le (by simp)
  have htoReal : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l)
      (fun out => ∃ y, out.1 = some y)).toReal
      = roundSuccessMass (sourceQSearchRound A hA j₀ S l) := rfl
  have hsucc_ge : ENNReal.ofReal (1 / 4)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y) := by
    rw [ENNReal.ofReal_le_iff_le_toReal (b := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l)
      (fun out => ∃ y, out.1 = some y)) hsucc_ne]
    rw [htoReal]
    linarith
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
  have hsum : ENNReal.ofReal (1 / 4)
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none) ≤ 1 := by
    calc ENNReal.ofReal (1 / 4)
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
          add_le_add hsucc_ge (le_refl _)
      _ = 1 := hpart
  have hle : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ (1:ℝ≥0∞) - ENNReal.ofReal (1 / 4) :=
    ENNReal.le_sub_of_add_le_left (by norm_num : (ENNReal.ofReal (1/4:ℝ)) ≠ ∞) hsum
  have hsub : ENNReal.ofReal (3 / 4) = (1:ℝ≥0∞) - ENNReal.ofReal (1 / 4) := by
    have hval : (1 - 1 / 4 : ℝ) = 3 / 4 := by ring
    rw [← hval, ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/4)]
    simp
  rw [← hsub] at hle
  exact hle

/-- A source loop with zero rounds has zero expected ledger value whenever the ledger vanishes
at the empty outcome. -/
theorem sourceLoop_ledger_expectation_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℝ≥0∞) (hL0 : L (none, 0, 0) = 0) (off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S 0 off) L = 0 := by
  simp only [sourceQSearchLoop, windowLoop_zero_eq,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  exact hL0

/-- An additive source-loop ledger is bounded by K(6/5)^(off + 1) when every round fails with
probability at most 1/4 and the round costs and K satisfy the stated recurrence inequality. -/
theorem sourceLoop_closed_quarter {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0)
    (c K : ℝ) (hc0 : 0 ≤ c) (hK0 : 0 ≤ K) (hK : c + (1/4) * K * (6/5) ≤ K)
    (hcost : ∀ l : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) L
      ≤ ENNReal.ofReal (c * ((6/5:ℝ)^l)))
    (hfail : ∀ l : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
        ≤ ENNReal.ofReal (1/4)) :
    ∀ T off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T off) L
        ≤ ENNReal.ofReal (K * ((6/5:ℝ)^(off+1))) := by
  intro T off
  induction T generalizing off with
  | zero =>
      have hz := sourceLoop_ledger_expectation_zero A hA j₀ S L hL0 off
      rw [hz]
      have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
      have hkn : (0:ℝ) ≤ K * ((6/5:ℝ)^(off+1)) := mul_nonneg hK0 hx
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hkn
  | succ T ih =>
      have hrec := windowLoop_ledger_expectation_succ A hA j₀ S (sourceQSearchRound A hA j₀ S)
        L hL T off
      have hIH := ih (off+1)
      simp only [sourceQSearchLoop] at hrec hIH ⊢
      rw [hrec]
      have hcost' := hcost (off+1)
      have hfail' := hfail (off+1)
      have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
      have hmul : (ENNReal.ofReal (1/4)) * ENNReal.ofReal (K * ((6/5:ℝ)^(off+2)))
          = ENNReal.ofReal ((1/4) * K * ((6/5:ℝ)^(off+2))) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
        congr 1
        ring
      have hpow : ((6/5:ℝ)^(off+2)) = ((6/5:ℝ)^(off+1)) * (6/5) := by
        have h2 := pow_succ (6/5:ℝ) (off+1)
        rw [show off+1+1 = off+2 from by omega] at h2
        exact h2
      have hstep : (1/4) * K * ((6/5:ℝ)^(off+2))
          = ((6/5:ℝ)^(off+1)) * ((1/4) * K * (6/5)) := by
        rw [hpow]
        ring
      have hadd : ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
            + ENNReal.ofReal (((6/5:ℝ)^(off+1)) * ((1/4) * K * (6/5)))
          = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (1/4) * K * (6/5))) := by
        rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ c * ((6/5:ℝ)^(off+1)))
          (by positivity : (0:ℝ) ≤ ((6/5:ℝ)^(off+1)) * ((1/4) * K * (6/5)))]
        congr 1
        ring
      have hfinal : ((6/5:ℝ)^(off+1)) * (c + (1/4) * K * (6/5))
          ≤ ((6/5:ℝ)^(off+1)) * K :=
        mul_le_mul_of_nonneg_left hK hx
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
              + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                    (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
              + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                    (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L := rfl
        _ ≤ ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + (ENNReal.ofReal (1/4)) * ENNReal.ofReal (K * ((6/5:ℝ)^(off+2))) :=
            add_le_add hcost' (mul_le_mul' hfail' hIH)
        _ = ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal ((1/4) * K * ((6/5:ℝ)^(off+2))) := by rw [hmul]
        _ = ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal (((6/5:ℝ)^(off+1)) * ((1/4) * K * (6/5))) := by
            rw [hstep]
        _ = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (1/4) * K * (6/5))) := hadd
        _ ≤ ENNReal.ofReal (K * ((6/5:ℝ)^(off+1))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [hfinal]

/-- Starting in the mature region, an additive source-loop ledger is bounded by K(6/5)^(off + 1)
under the round cost bound, failure bound 3/4, and stated recurrence inequality. -/
theorem sourceLoop_closed_mature {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ls : ℕ)
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0)
    (c K : ℝ) (hc0 : 0 ≤ c) (hK0 : 0 ≤ K) (hK : c + (3/4) * K * (6/5) ≤ K)
    (hcost : ∀ l : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) L
      ≤ ENNReal.ofReal (c * ((6/5:ℝ)^l)))
    (hfail : ∀ l : ℕ, ls ≤ l →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
        ≤ ENNReal.ofReal (3/4)) :
    ∀ T off : ℕ, ls ≤ off+1 →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T off) L
        ≤ ENNReal.ofReal (K * ((6/5:ℝ)^(off+1))) := by
  intro T off
  induction T generalizing off with
  | zero =>
      intro hoff
      have hz := sourceLoop_ledger_expectation_zero A hA j₀ S L hL0 off
      rw [hz]
      have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
      have hkn : (0:ℝ) ≤ K * ((6/5:ℝ)^(off+1)) := mul_nonneg hK0 hx
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hkn
  | succ T ih =>
      intro hoff
      have hrec := windowLoop_ledger_expectation_succ A hA j₀ S (sourceQSearchRound A hA j₀ S)
        L hL T off
      have hIH := ih (off+1) (by omega)
      simp only [sourceQSearchLoop] at hrec hIH ⊢
      rw [hrec]
      have hcost' := hcost (off+1)
      have hfail' := hfail (off+1) hoff
      have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
      have hmul : (ENNReal.ofReal (3/4)) * ENNReal.ofReal (K * ((6/5:ℝ)^(off+2)))
          = ENNReal.ofReal ((3/4) * K * ((6/5:ℝ)^(off+2))) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4)]
        congr 1
        ring
      have hpow : ((6/5:ℝ)^(off+2)) = ((6/5:ℝ)^(off+1)) * (6/5) := by
        have h2 := pow_succ (6/5:ℝ) (off+1)
        rw [show off+1+1 = off+2 from by omega] at h2
        exact h2
      have hstep : (3/4) * K * ((6/5:ℝ)^(off+2))
          = ((6/5:ℝ)^(off+1)) * ((3/4) * K * (6/5)) := by
        rw [hpow]
        ring
      have hadd : ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
            + ENNReal.ofReal (((6/5:ℝ)^(off+1)) * ((3/4) * K * (6/5)))
          = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (3/4) * K * (6/5))) := by
        rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ c * ((6/5:ℝ)^(off+1)))
          (by positivity : (0:ℝ) ≤ ((6/5:ℝ)^(off+1)) * ((3/4) * K * (6/5)))]
        congr 1
        ring
      have hfinal : ((6/5:ℝ)^(off+1)) * (c + (3/4) * K * (6/5))
          ≤ ((6/5:ℝ)^(off+1)) * K :=
        mul_le_mul_of_nonneg_left hK hx
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
              + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                    (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
              + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                    (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L := rfl
        _ ≤ ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + (ENNReal.ofReal (3/4)) * ENNReal.ofReal (K * ((6/5:ℝ)^(off+2))) :=
            add_le_add hcost' (mul_le_mul' hfail' hIH)
        _ = ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal ((3/4) * K * ((6/5:ℝ)^(off+2))) := by rw [hmul]
        _ = ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal (((6/5:ℝ)^(off+1)) * ((3/4) * K * (6/5))) := by
            rw [hstep]
        _ = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (3/4) * K * (6/5))) := hadd
        _ ≤ ENNReal.ofReal (K * ((6/5:ℝ)^(off+1))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [hfinal]

/-- Before the mature threshold, the loop's expected ledger plus the stated geometric reserve is
at most B(6/5)^ls, assuming the given cost, failure, mature-region, and coefficient bounds. -/
theorem sourceLoop_closed_immature {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ls : ℕ)
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0)
    (c A' B Km : ℝ) (hc0 : 0 ≤ c) (hA'0 : 0 ≤ A') (hB0 : 0 ≤ B) (hKm0 : 0 ≤ Km)
    (hA' : c + A' ≤ (6/5) * A') (hAB : A' ≤ B)
    (hB : c + (3/4) * Km * (6/5) + A' ≤ B)
    (hcost : ∀ l : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) L
      ≤ ENNReal.ofReal (c * ((6/5:ℝ)^l)))
    (hfailm : ∀ l : ℕ, ls ≤ l →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
        ≤ ENNReal.ofReal (3/4))
    (hmature : ∀ T off : ℕ, ls ≤ off+1 →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T off) L
        ≤ ENNReal.ofReal (Km * ((6/5:ℝ)^(off+1)))) :
    ∀ T off : ℕ, off+1 ≤ ls →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T off) L
        + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1)))
        ≤ ENNReal.ofReal (B * ((6/5:ℝ)^ls)) := by
  intro T off
  induction T generalizing off with
  | zero =>
      intro hoff
      have hz := sourceLoop_ledger_expectation_zero A hA j₀ S L hL0 off
      rw [hz, zero_add]
      have hmono : ((6/5:ℝ)^(off+1)) ≤ ((6/5:ℝ)^ls) := sourceGeopow_mono (by omega)
      have hxls : (0:ℝ) ≤ ((6/5:ℝ)^ls) := by positivity
      have hab : A' * ((6/5:ℝ)^(off+1)) ≤ B * ((6/5:ℝ)^ls) := by
        calc A' * ((6/5:ℝ)^(off+1)) ≤ A' * ((6/5:ℝ)^ls) :=
              mul_le_mul_of_nonneg_left hmono hA'0
          _ ≤ B * ((6/5:ℝ)^ls) := mul_le_mul_of_nonneg_right hAB hxls
      exact ENNReal.ofReal_le_ofReal hab
  | succ T ih =>
      intro hoff
      have hrec := windowLoop_ledger_expectation_succ A hA j₀ S (sourceQSearchRound A hA j₀ S)
        L hL T off
      simp only [sourceQSearchLoop] at hrec ⊢
      rw [hrec]
      have hcost' := hcost (off+1)
      have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
      have hpow : ((6/5:ℝ)^(off+2)) = ((6/5:ℝ)^(off+1)) * (6/5) := by
        have h2 := pow_succ (6/5:ℝ) (off+1)
        rw [show off+1+1 = off+2 from by omega] at h2
        exact h2
      rcases Nat.lt_or_ge (off+1) ls with hlt | hge
      · have hfail' : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1))
              (fun out => out.1 = none) ≤ 1 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
        have hIH := ih (off+1) (by omega)
        have hstep : ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1)))
            ≤ ENNReal.ofReal (A' * ((6/5:ℝ)^(off+2))) := by
          rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ c * ((6/5:ℝ)^(off+1)))
            (by positivity : (0:ℝ) ≤ A' * ((6/5:ℝ)^(off+1)))]
          refine ENNReal.ofReal_le_ofReal ?_
          have hmul := mul_le_mul_of_nonneg_left hA' hx
          calc c * ((6/5:ℝ)^(off+1)) + A' * ((6/5:ℝ)^(off+1))
              = (c + A') * ((6/5:ℝ)^(off+1)) := by ring
            _ ≤ (6/5) * A' * ((6/5:ℝ)^(off+1)) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using! hmul
            _ = A' * (((6/5:ℝ)^(off+1)) * (6/5)) := by ring
            _ = A' * ((6/5:ℝ)^(off+2)) := by rw [hpow]
        calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
                + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                  * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                      (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1)))
            = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
                + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                  * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                      (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := rfl
            _ ≤ (ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
                  + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                      (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L)
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := by
                  refine add_le_add (add_le_add hcost' ?_) le_rfl
                  calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1))
                          (fun out => out.1 = none)
                      * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                          (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                      ≤ (1:ℝ≥0∞)
                          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                            (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L :=
                        mul_le_mul' hfail' le_rfl
                    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                        (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L :=
                      one_mul _
            _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                  (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + (ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
                  + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1)))) := by ring
            _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                  (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+2))) := by
                  refine add_le_add le_rfl ?_
                  exact hstep
            _ ≤ ENNReal.ofReal (B * ((6/5:ℝ)^ls)) := hIH
      · have hoffeq : off+1 = ls := by omega
        have hfailm' := hfailm (off+1) (by omega)
        have hmature' := hmature T (off+1) (by omega)
        have hmul : (ENNReal.ofReal (3/4)) * ENNReal.ofReal (Km * ((6/5:ℝ)^(off+2)))
            = ENNReal.ofReal ((3/4) * Km * ((6/5:ℝ)^(off+2))) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4)]
          congr 1
          ring
        have hstep : (3/4) * Km * ((6/5:ℝ)^(off+2))
            = ((6/5:ℝ)^(off+1)) * ((3/4) * Km * (6/5)) := by
          rw [hpow]
          ring
        calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
                + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                  * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                      (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1)))
            = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (off+1)) L
                + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
                  * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                      (windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S) T (off+1)) L
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := rfl
            _ ≤ (ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
                  + (ENNReal.ofReal (3/4)) * ENNReal.ofReal (Km * ((6/5:ℝ)^(off+2))))
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := by
                  refine add_le_add (add_le_add hcost' (mul_le_mul' hfailm' hmature')) le_rfl
            _ = ENNReal.ofReal (c * ((6/5:ℝ)^(off+1)))
                + ENNReal.ofReal ((3/4) * Km * ((6/5:ℝ)^(off+2)))
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := by rw [hmul]
            _ = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (3/4) * Km * (6/5)))
                + ENNReal.ofReal (A' * ((6/5:ℝ)^(off+1))) := by
                rw [hstep, ← ENNReal.ofReal_add
                  (by positivity : (0:ℝ) ≤ c * ((6/5:ℝ)^(off+1)))
                  (by positivity : (0:ℝ) ≤ ((6/5:ℝ)^(off+1)) * ((3/4) * Km * (6/5)))]
                congr 1
                ring
            _ = ENNReal.ofReal (((6/5:ℝ)^(off+1)) * (c + (3/4) * Km * (6/5) + A')) := by
                rw [← ENNReal.ofReal_add
                  (by positivity : (0:ℝ) ≤ ((6/5:ℝ)^(off+1)) * (c + (3/4) * Km * (6/5)))
                  (by positivity : (0:ℝ) ≤ A' * ((6/5:ℝ)^(off+1)))]
                congr 1
                ring
            _ ≤ ENNReal.ofReal (B * ((6/5:ℝ)^ls)) := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [hoffeq]
                have hxls : (0:ℝ) ≤ ((6/5:ℝ)^ls) := by positivity
                nlinarith [mul_le_mul_of_nonneg_left hB hxls]

/-- For every positive real s, some positive exponent k satisfies (6/5)^k s ≥ 1. -/
theorem sourceExists_geometric_cross {s : ℝ} (hs : 0 < s) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ ((6/5:ℝ)^k)*s := by
  have hgrowth : ∀ k : ℕ, 1 + (k:ℝ)/5 ≤ ((6/5:ℝ)^k) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc (1:ℝ) + (((k+1:ℕ):ℝ))/5 ≤ (6/5:ℝ) * (1 + (k:ℝ)/5) := by
              have heq : (1:ℝ) + ((k+1:ℕ):ℝ)/5 + (k:ℝ)/25
                  = (6/5:ℝ) * (1 + (k:ℝ)/5) := by
                push_cast
                field_simp
                ring
              have hk25 : (0:ℝ) ≤ (k:ℝ)/25 := by positivity
              linarith
          _ ≤ (6/5:ℝ) * ((6/5:ℝ)^k) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (6/5:ℝ)^(k+1) := (pow_succ' _ _).symm
  refine ⟨max 1 (Nat.ceil (5/s)), Nat.le_max_left 1 _, ?_⟩
  have hceil5 : (5/s) ≤ ((Nat.ceil (5/s) : ℕ):ℝ) := Nat.le_ceil (5/s)
  have hmax1 : (5/s) ≤ ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ) := by
    calc (5/s) ≤ ((Nat.ceil (5/s) : ℕ):ℝ) := hceil5
      _ ≤ ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ) := by
          exact_mod_cast Nat.le_max_right 1 (Nat.ceil (5/s))
  have h1 : (1:ℝ) + ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ)/5 ≥ 1 + (5/s)/5 := by
    apply add_le_add (le_refl 1)
    exact div_le_div_of_nonneg_right hmax1 (by norm_num)
  have h2 : (1:ℝ) + (5/s)/5 = 1 + 1/s := by field_simp
  have hgrow := hgrowth (max 1 (Nat.ceil (5/s)))
  simp only [Nat.cast_max, Nat.cast_one] at hgrow
  have hkey : 1/s ≤ ((6/5:ℝ)^(max 1 (Nat.ceil (5/s)))) := by
    calc 1/s ≤ 1 + 1/s := by linarith
      _ = 1 + (5/s)/5 := h2.symm
      _ ≤ 1 + ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ)/5 := h1
      _ ≤ (6/5:ℝ)^(max 1 (Nat.ceil (5/s))) := hgrow
  calc (1:ℝ) = (1/s) * s := by field_simp
    _ ≤ ((6/5:ℝ)^(max 1 (Nat.ceil (5/s)))) * s :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hs)

/-- For 0 < s ≤ 1, there is a positive threshold ls with (6/5)^ls s ≤ 6/5 such that (6/5)^l s ≥
1 for every l ≥ ls. -/
theorem sourceExists_crossing {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ ls : ℕ, 1 ≤ ls ∧ ((6/5:ℝ)^ls)*s ≤ 6/5 ∧
      ∀ l : ℕ, ls ≤ l → 1 ≤ ((6/5:ℝ)^l)*s := by
  have hex : ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ ((6/5:ℝ)^k)*s := sourceExists_geometric_cross hs0
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
  · rcases Nat.lt_or_ge 1 (Nat.find hex) with h2 | h2
    · have hmin : ¬ (1 ≤ (Nat.find hex) - 1 ∧ 1 ≤ ((6/5:ℝ)^((Nat.find hex) - 1))*s) :=
        Nat.find_min hex (by omega)
      have hlt : ((6/5:ℝ)^((Nat.find hex) - 1))*s < 1 := by
        by_cases hc : ((6/5:ℝ)^((Nat.find hex) - 1))*s < 1
        · exact hc
        · push Not at hc
          exact absurd ⟨by omega, hc⟩ hmin
      have hexp : ((6/5:ℝ)^(Nat.find hex))*s
          = (6/5:ℝ)*(((6/5:ℝ)^((Nat.find hex) - 1))*s) := by
        have h := pow_succ (6/5:ℝ) ((Nat.find hex) - 1)
        rw [show (Nat.find hex) - 1 + 1 = Nat.find hex from by omega] at h
        rw [h]
        ring
      rw [hexp]
      calc (6/5:ℝ)*(((6/5:ℝ)^((Nat.find hex) - 1))*s)
          ≤ (6/5:ℝ)*1 := mul_le_mul_of_nonneg_left (le_of_lt hlt) (by norm_num)
        _ = 6/5 := mul_one _
    · have h1 : Nat.find hex = 1 := le_antisymm h2 (Nat.find_spec hex).1
      rw [h1, pow_one]
      calc (6/5:ℝ)*s ≤ (6/5:ℝ)*1 := mul_le_mul_of_nonneg_left hs1 (by norm_num)
        _ = 6/5 := mul_one _
  · intro l hl
    have hmono : ((6/5:ℝ)^(Nat.find hex)) ≤ ((6/5:ℝ)^l) := sourceGeopow_mono hl
    calc (1:ℝ) ≤ ((6/5:ℝ)^(Nat.find hex))*s := (Nat.find_spec hex).2
      _ ≤ ((6/5:ℝ)^l)*s := mul_le_mul_of_nonneg_right hmono (le_of_lt hs0)

/-- Under the stated additive-ledger, geometric cost, and coefficient hypotheses, every finite
source loop has expected ledger at most 400/√a when its initial marked probability a is
positive. -/
theorem sourceLoop_ledger_expectation_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℝ≥0∞)
    (hL : ∀ (r out : Option I × ℕ × ℕ),
      L (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) = L r + L out)
    (hL0 : L (none, 0, 0) = 0)
    (c Kq Km A' B : ℝ) (hc0 : 0 ≤ c)
    (hKq : c + (1/4) * Kq * (6/5) ≤ Kq) (hKq400 : Kq * (6/5) ≤ 400)
    (hKm : c + (3/4) * Km * (6/5) ≤ Km)
    (hA' : c + A' ≤ (6/5) * A') (hAB : A' ≤ B)
    (hB : c + (3/4) * Km * (6/5) + A' ≤ B) (hB400 : B * (6/5) ≤ 400)
    (hcost : ∀ l : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) L
      ≤ ENNReal.ofReal (c * ((6/5:ℝ)^l)))
    (ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S)
    (ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1)
    (T : ℕ) (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) L
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) := by
  have hsqrt : (0:ℝ) < Real.sqrt (MeasureProb (preparedAAState A j₀) S) :=
    Real.sqrt_pos.mpr ha
  rcases lt_or_ge (MeasureProb (preparedAAState A j₀) S) (3/4) with h34 | h43
  · have hsqlt : Real.sqrt (MeasureProb (preparedAAState A j₀) S) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
      linarith
    have hsθ : Real.sin (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)))
        = Real.sqrt (MeasureProb (preparedAAState A j₀) S) :=
      Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ) ≤ 0) (Real.sqrt_nonneg _))
        (Real.sqrt_le_one.mpr ha1)
    have hθ0 : 0 < Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
      Real.arcsin_pos.mpr hsqrt
    have hθ1 : Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)) < Real.pi/2 :=
      Real.arcsin_lt_pi_div_two.mpr hsqlt
    have hmass : MeasureProb (preparedAAState A j₀) S
        = (Real.sin (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))))^2 := by
      rw [hsθ, Real.sq_sqrt ha0]
    have hsin2 : Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)))
        = 2 * Real.sqrt (MeasureProb (preparedAAState A j₀) S)
            * Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := by
      rw [Real.sin_two_mul, hsθ, Real.cos_arcsin, Real.sq_sqrt ha0]
    have hsin2pos : 0 < Real.sin
        (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      rw [hsin2]
      exact mul_pos (mul_pos (by norm_num) hsqrt)
        (Real.sqrt_pos.mpr (by linarith))
    have hge : Real.sqrt (MeasureProb (preparedAAState A j₀) S)
        ≤ Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      rw [hsin2]
      have h1a : (1:ℝ)/2 ≤ Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := by
        have hq : ((1:ℝ)/2)^2 ≤ 1 - MeasureProb (preparedAAState A j₀) S := by
          nlinarith [h34]
        calc (1:ℝ)/2 = Real.sqrt (((1:ℝ)/2)^2) := (Real.sqrt_sq (by norm_num)).symm
          _ ≤ Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := Real.sqrt_le_sqrt hq
      have hkey : (0:ℝ) ≤ Real.sqrt (MeasureProb (preparedAAState A j₀) S)
          * (2 * Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) - 1) :=
        mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)
      nlinarith [hkey]
    obtain ⟨ls, hls1, hlsbound, hlsmature⟩ :=
      sourceExists_crossing hsin2pos (Real.sin_le_one _)
    have hwinmat : ∀ l : ℕ, ls ≤ l → 1 ≤ (qSearchWindow l : ℝ)
        *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      intro l hl
      have h1 : 1 ≤ ((6/5:ℝ)^l)
          *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
        hlsmature l hl
      calc (1:ℝ) ≤ ((6/5:ℝ)^l)
          *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := h1
        _ ≤ (qSearchWindow l : ℝ)
            *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
            mul_le_mul_of_nonneg_right (sourceWindow_ge l) (le_of_lt hsin2pos)
    have hfailm : ∀ l : ℕ, ls ≤ l →
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
          ≤ ENNReal.ofReal (3 / 4) := by
      intro l hl
      refine sourceFailMass_le_three_quarters A hA j₀ S
        (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) l hθ0 hθ1 hmass ?_

      have h1 : 1 ≤ (qSearchWindow l : ℝ)
          * Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
        hwinmat l hl
      have h2 : (qSearchWindow l : ℝ)
          ≤ (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) := by
        have hcast : (((qSearchWindow l : ℕ) + 1 : ℕ) : ℝ) = (qSearchWindow l : ℝ) + 1 := by
          rw [Nat.cast_add]
          simp
        rw [hcast]
        linarith
      have hsin2_nonneg : (0:ℝ)
          ≤ Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
        le_of_lt hsin2pos
      have h3 := mul_le_mul_of_nonneg_right h2 hsin2_nonneg
      nlinarith [h1, h3]
    have hKm0 : (0:ℝ) ≤ Km := by
      have := hKm
      linarith
    have hA'0 : (0:ℝ) ≤ A' := by
      have := hA'
      linarith
    have hB0 : (0:ℝ) ≤ B := by
      have := hB
      linarith
    have hmature := sourceLoop_closed_mature A hA j₀ S ls L hL hL0 (c := c) (K := Km)
      hc0 hKm0 hKm hcost hfailm
    have himm := sourceLoop_closed_immature A hA j₀ S ls L hL hL0
      (c := c) (A' := A') (B := B) (Km := Km)
      hc0 hA'0 hB0 hKm0 hA' hAB hB hcost hfailm hmature
    have himm0 := himm T 0 (by omega)
    have hle := le_trans (le_add_right (le_refl _)) himm0
    refine le_trans hle ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : ((6/5:ℝ)^ls)
        ≤ (6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      calc ((6/5:ℝ)^ls) * Real.sqrt (MeasureProb (preparedAAState A j₀) S)
          ≤ ((6/5:ℝ)^ls)
              *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
            mul_le_mul_of_nonneg_left hge (pow_nonneg (by norm_num : (0:ℝ) ≤ 6/5) ls)
        _ ≤ 6/5 := hlsbound
    have h1 : B * ((6/5:ℝ)^ls)
        ≤ B * ((6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h2 : B * ((6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S))
        ≤ 400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hsqrt)]
      exact hB400
    exact le_trans h1 h2
  · have hfail : ∀ l : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => out.1 = none)
          ≤ ENNReal.ofReal (1/4) := by
      intro l
      refine le_trans (sourceRound_fail_mass_le A hA j₀ S l) ?_
      rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_sub 1 ha0]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    have hKq0 : (0:ℝ) ≤ Kq := by
      have := hKq
      linarith
    have hE := sourceLoop_closed_quarter A hA j₀ S L hL hL0 (c := c) (K := Kq)
      hc0 hKq0 hKq hcost hfail T 0
    refine le_trans hE ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : ((6/5:ℝ)^(0+1)) = 6/5 := by rw [Nat.zero_add, pow_one]
    have h400 : (400:ℝ) ≤ 400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      nlinarith [Real.sqrt_le_one.mpr ha1]
    rw [hp]
    nlinarith [hKq400]

/-- For positive initial marked probability a, the expected first ledger of every finite source
loop is at most 400/√a. -/
theorem sourceLoop_ledger1_expectation_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) := by
  have hL : ∀ (r out : Option I × ℕ × ℕ),
      (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞))
        (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)
        = (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) r
          + (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) out := by
    intro r out
    obtain ⟨_, r2, _⟩ := r
    obtain ⟨_, o2, _⟩ := out
    simp [Nat.cast_add]
  have hL0 : (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) (none, 0, 0) = 0 := by simp
  have hcost : ∀ l : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) := fun l =>
    sourceRound_ledger1_expectation_le A hA j₀ S l
  refine sourceLoop_ledger_expectation_le A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞)) hL hL0
    6 12 60 36 96 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcost ?_ ?_ T ha
  · have hsq : (6:ℝ) + (1/4) * 12 * (6/5) ≤ 12 := by norm_num
    linarith
  · have hsq : (12:ℝ) * (6/5) ≤ 400 := by norm_num
    linarith
  · have hsq : (6:ℝ) + (3/4) * 60 * (6/5) ≤ 60 := by norm_num
    linarith
  · have hsq : (6:ℝ) + 36 ≤ (6/5) * 36 := by norm_num
    linarith
  · have hsq : (36:ℝ) ≤ 96 := by norm_num
    linarith
  · have hsq : (6:ℝ) + (3/4) * 60 * (6/5) + 36 ≤ 96 := by norm_num
    linarith
  · have hsq : (96:ℝ) * (6/5) ≤ 400 := by norm_num
    linarith
  · exact measureProb_nonneg _ _
  · exact measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S

/-- For positive initial marked probability a, the expected second ledger of every finite source
loop is at most 400/√a. -/
theorem sourceLoop_ledger2_expectation_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) := by
  have hL : ∀ (r out : Option I × ℕ × ℕ),
      (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞))
        (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)
        = (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) r
          + (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) out := by
    intro r out
    obtain ⟨_, r2, _⟩ := r
    obtain ⟨_, o2, _⟩ := out
    simp [Nat.cast_add]
  have hL0 : (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) (none, 0, 0) = 0 := by simp
  have hcost : ∀ l : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) := fun l =>
    sourceRound_ledger2_expectation_le A hA j₀ S l
  refine sourceLoop_ledger_expectation_le A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞)) hL hL0
    4 8 40 24 64 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcost ?_ ?_ T ha
  · have hsq : (4:ℝ) + (1/4) * 8 * (6/5) ≤ 8 := by norm_num
    linarith
  · have hsq : (8:ℝ) * (6/5) ≤ 400 := by norm_num
    linarith
  · have hsq : (4:ℝ) + (3/4) * 40 * (6/5) ≤ 40 := by norm_num
    linarith
  · have hsq : (4:ℝ) + 24 ≤ (6/5) * 24 := by norm_num
    linarith
  · have hsq : (24:ℝ) ≤ 64 := by norm_num
    linarith
  · have hsq : (4:ℝ) + (3/4) * 40 * (6/5) + 24 ≤ 64 := by norm_num
    linarith
  · have hsq : (64:ℝ) * (6/5) ≤ 400 := by norm_num
    linarith
  · exact measureProb_nonneg _ _
  · exact measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S

/-- For positive initial marked probability a, both infinite source-search ledger expectation
series are at most 400/√a. -/
theorem sourceStopLedgerExpectation_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
    sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) := by
  have hL1 : ∀ (r out : Option I × ℕ × ℕ),
      (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞))
        (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)
        = (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) r
          + (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) out := by
    intro r out
    obtain ⟨_, r2, _⟩ := r
    obtain ⟨_, o2, _⟩ := out
    simp [Nat.cast_add]
  have hL1_0 : (fun o : Option I × ℕ × ℕ => (o.2.1 : ℝ≥0∞)) (none, 0, 0) = 0 := by simp
  have hL2 : ∀ (r out : Option I × ℕ × ℕ),
      (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞))
        (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)
        = (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) r
          + (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) out := by
    intro r out
    obtain ⟨_, r2, _⟩ := r
    obtain ⟨_, o2, _⟩ := out
    simp [Nat.cast_add]
  have hL2_0 : (fun o : Option I × ℕ × ℕ => (o.2.2 : ℝ≥0∞)) (none, 0, 0) = 0 := by simp
  have hunfold1 : ∀ T,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0)
          (fun out => (out.2.1 : ℝ≥0∞))
        = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
              (fun out => (out.2.1 : ℝ≥0∞)) :=
    sourceQSearchLoop_ledger_expectation_unfold A hA j₀ S
      (fun out => (out.2.1 : ℝ≥0∞)) hL1 hL1_0
  have hunfold2 : ∀ T,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0)
          (fun out => (out.2.2 : ℝ≥0∞))
        = ∑ i ∈ Finset.range T, sourceReachMass A hA j₀ S i
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchRound A hA j₀ S (i + 1))
              (fun out => (out.2.2 : ℝ≥0∞)) :=
    sourceQSearchLoop_ledger_expectation_unfold A hA j₀ S
      (fun out => (out.2.2 : ℝ≥0∞)) hL2 hL2_0
  constructor
  · unfold sourceStopLedgerExpectation
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun T => ?_)
    rw [← hunfold1 T]
    exact sourceLoop_ledger1_expectation_le A hA j₀ S T ha
  · unfold sourceStopLedgerExpectation
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun T => ?_)
    rw [← hunfold2 T]
    exact sourceLoop_ledger2_expectation_le A hA j₀ S T ha
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
