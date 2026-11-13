/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ExactVaRProgramDefs

/-!
# Real-valued market CDFs and truncation

This module defines population and empirical CDFs for a finite market with real-valued losses.
It proves a sampling bound, describes how capping losses changes the CDF and tail mass, and
evaluates a two-atom example.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `marketCDF_sampling_bound`: For `N > 0` and `ν > 0`, the probability of empirical CDF error
  greater than `ν` is at most `1 / (4 * N * ν²)`.
* `truncated_CDF_eq_below`: Capping losses at `T` preserves the CDF at every threshold strictly
  below `T`.
* `market_tail_gap`: The complement of the CDF at `T` is the strict upper-tail mass above `T`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

/-- The population CDF of real-valued losses under a finite market distribution. -/
noncomputable def marketCDF {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) : ℝ :=
  ∑ a, p.prob a * (if loss a ≤ t then 1 else 0)

/-- The empirical CDF of real-valued losses, given by the fraction of the `N` samples at or
below the threshold. -/
noncomputable def marketEmpiricalCDF {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) : ℝ :=
  (∑ k, if loss (ω k) ≤ t then 1 else 0) / N

/-- The real-valued indicator of the event that loss is at most the threshold. -/
noncomputable def marketIndicator {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : ℝ := if loss a ≤ t then 1 else 0

/-- The market threshold indicator takes only the values zero and one. -/
theorem marketIndicator_mem {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : marketIndicator loss t a = 0 ∨ marketIndicator loss t a = 1 := by
  unfold marketIndicator
  split_ifs <;> norm_num

/-- The market threshold indicator is at most one. -/
theorem marketIndicator_le_one {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : marketIndicator loss t a ≤ 1 := by
  unfold marketIndicator
  split_ifs <;> norm_num

/-- The market CDF is the expectation of its threshold indicator. -/
theorem marketCDF_eq_expect {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) :
    marketCDF p loss t = p.expect (marketIndicator loss t) := by
  unfold marketCDF FinDist.expect
  rfl

/-- The empirical market CDF is the sample average of its threshold indicator. -/
theorem marketEmpiricalCDF_eq_avg {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) :
    marketEmpiricalCDF ω loss t = FinDist.avg (marketIndicator loss t) ω := by
  unfold marketEmpiricalCDF FinDist.avg
  rfl

/-- The variance of the market threshold indicator is at most one quarter. -/
theorem marketIndicator_variance {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) :
    p.variance (marketIndicator loss t) ≤ 1/4 := by
  let f := marketIndicator loss t
  let μ := p.expect f
  have hsq a : (f a)^2 = f a := by
    change (marketIndicator loss t a)^2 = marketIndicator loss t a
    rcases marketIndicator_mem loss t a with h | h
    · rw [h]
      ring
    · rw [h]
      ring
  have he a : p.prob a*(f a-μ)^2 =
      p.prob a*f a-(2*μ)*(p.prob a*f a)+μ^2*p.prob a := by
    calc
      _ = p.prob a*(f a)^2-(2*μ)*(p.prob a*f a)+μ^2*p.prob a := by ring
      _ = _ := by rw [hsq a]
  have hv : p.variance f = μ-μ^2 := by
    change (∑ a, p.prob a*(f a-μ)^2) = _
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, p.sum_one]
    change μ-(2*μ)*μ+μ^2*1=μ-μ^2
    ring
  rw [hv]
  nlinarith [sq_nonneg (μ-1/2)]

/-- For `N > 0` and `ν > 0`, the probability of empirical CDF error greater than `ν` is at most
`1 / (4 * N * ν²)`. -/
theorem marketCDF_sampling_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
      ν < |marketEmpiricalCDF ω loss t - marketCDF p loss t|)
      ≤ 1/(4*(N : ℝ)*ν^2) := by
  have h := p.chebyshev_avg (marketIndicator loss t) hN ν hν
  simp only [← marketEmpiricalCDF_eq_avg, FinDist.expect, marketIndicator] at h
  apply h.trans
  have hd : 0 < (N : ℝ)*ν^2 := mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hν)
  calc
    _ ≤ (1/4 : ℝ)/((N : ℝ)*ν^2) :=
      div_le_div_of_nonneg_right (marketIndicator_variance p loss t) hd.le
    _ = _ := by ring

/-- The loss capped above at `T`, defined pointwise by `min (loss a) T`. -/
noncomputable def truncatedLoss {n : ℕ} (loss : Option (Fin n) → ℝ) (T : ℝ)
    (a : Option (Fin n)) : ℝ := min (loss a) T

/-- Capping losses at `T` preserves the CDF at every threshold strictly below `T`. -/
theorem truncated_CDF_eq_below {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T t : ℝ) (ht : t < T) :
    marketCDF p (truncatedLoss loss T) t = marketCDF p loss t := by
  unfold marketCDF
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : loss a ≤ t
  · have hmin : truncatedLoss loss T a = loss a := by
      unfold truncatedLoss
      exact min_eq_left (ha.trans (le_of_lt ht))
    rw [hmin, if_pos ha]
  · have hpos : t < truncatedLoss loss T a := by
      unfold truncatedLoss
      exact lt_min (lt_of_not_ge ha) ht
    rw [if_neg (not_le_of_gt hpos), if_neg ha]

/-- The CDF of losses capped at `T` is one at every threshold at least `T`. -/
theorem truncated_CDF_eq_one_above {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T t : ℝ) (ht : T ≤ t) :
    marketCDF p (truncatedLoss loss T) t = 1 := by
  have hmin : ∀ a, truncatedLoss loss T a ≤ t := by
    intro a
    unfold truncatedLoss
    exact (min_le_right (loss a) T).trans ht
  unfold marketCDF
  calc
    (∑ a, p.prob a * (if truncatedLoss loss T a ≤ t then 1 else 0))
        = ∑ a, p.prob a * 1 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [if_pos (hmin a)]
    _ = 1 := by
      calc
        (∑ a, p.prob a * 1) = ∑ a, p.prob a := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = 1 := p.sum_one

/-- The CDF mass at `T` plus the strict upper-tail mass above `T` equals one. -/
theorem market_tail_mass {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T : ℝ) :
    marketCDF p loss T + (∑ a, p.prob a * (if T < loss a then 1 else 0)) = 1 := by
  have hsplit : ∀ a : Option (Fin n),
      ((if loss a ≤ T then (1:ℝ) else (0:ℝ)) + (if T < loss a then (1:ℝ) else (0:ℝ)))
        = (1:ℝ) := by
    intro a
    by_cases ha : loss a ≤ T
    · have hn : ¬ (T < loss a) := not_lt.mpr ha
      simp only [if_pos ha, if_neg hn]
      ring
    · have hn : T < loss a := lt_of_not_ge ha
      simp only [if_neg ha, if_pos hn]
      ring
  have hmain : (∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
      + (∑ a, p.prob a * (if T < loss a then 1 else 0)) = 1 := by
    rw [← Finset.sum_add_distrib]
    have hpoint : (∑ a, (p.prob a * (if loss a ≤ T then 1 else 0)
        + p.prob a * (if T < loss a then 1 else 0))) = ∑ a, p.prob a * 1 := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        p.prob a * (if loss a ≤ T then 1 else 0) + p.prob a * (if T < loss a then 1 else 0)
            = p.prob a * ((if loss a ≤ T then 1 else 0) + (if T < loss a then 1 else 0)) := by
              rw [← mul_add]
        _ = p.prob a * 1 := congrArg (fun z => p.prob a * z) (hsplit a)
    rw [hpoint]
    calc
      (∑ a, p.prob a * 1) = ∑ a, p.prob a := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 1 := p.sum_one
  unfold marketCDF
  exact hmain

/-- The complement of the CDF at `T` is the strict upper-tail mass above `T`. -/
theorem market_tail_gap {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T : ℝ) :
    1 - marketCDF p loss T = ∑ a, p.prob a * (if T < loss a then 1 else 0) := by
  have h := market_tail_mass p loss T
  unfold marketCDF at h
  have hA : (∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
      = 1 - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by
    calc
      (∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
          = ((∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
              + (∑ a, p.prob a * (if T < loss a then 1 else 0)))
            - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by ring
      _ = 1 - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by rw [h]
  unfold marketCDF
  rw [hA]
  ring

/-- The CDF at the cap equals one minus the strict upper-tail mass of the original losses. -/
theorem market_cdf_at_cap_eq_one_sub_tail {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T : ℝ) :
    marketCDF p loss T = 1 - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by
  have h := market_tail_mass p loss T
  unfold marketCDF at h
  calc
    marketCDF p loss T
        = (∑ a, p.prob a * (if loss a ≤ T then 1 else 0)) := rfl
    _ = 1 - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by
        calc
          (∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
              = ((∑ a, p.prob a * (if loss a ≤ T then 1 else 0))
                  + (∑ a, p.prob a * (if T < loss a then 1 else 0)))
                - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by ring
          _ = 1 - (∑ a, p.prob a * (if T < loss a then 1 else 0)) := by rw [h]

/-- The capped-loss CDF equals one at the cap. -/
theorem truncated_CDF_at_cap_one {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (T : ℝ) :
    marketCDF p (truncatedLoss loss T) T = 1 :=
  truncated_CDF_eq_one_above p loss T T (le_refl T)

/-- The two-atom example loss, equal to one half at `some 1` and zero elsewhere. -/
noncomputable def continuousTwoAtomLoss (x : Option (Fin 2)) : ℝ :=
  if x = some 1 then (1/2 : ℝ) else 0

/-- For the two-atom population with weight `a`, the real-loss CDF at zero is `a`. -/
theorem continuousTwoAtom_cdf_zero (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    marketCDF (twoAtomPop a ha0 ha1) continuousTwoAtomLoss 0 = a := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold marketCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if continuousTwoAtomLoss x ≤ 0 then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if continuousTwoAtomLoss (some y) ≤ 0 then 1 else 0)))
  rw [h, h2]
  simp [twoAtomProb, continuousTwoAtomLoss]

/-- The real-loss two-atom CDF at one half is one. -/
theorem continuousTwoAtom_cdf_half (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    marketCDF (twoAtomPop a ha0 ha1) continuousTwoAtomLoss (1/2) = 1 := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold marketCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if continuousTwoAtomLoss x ≤ 1/2 then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if continuousTwoAtomLoss (some y) ≤ 1/2 then 1 else 0)))
  rw [h, h2]
  simp [twoAtomProb, continuousTwoAtomLoss]

/-- For the two-atom population with weight `a`, the real-loss CDF at one quarter is `a`. -/
theorem continuousTwoAtom_cdf_quarter (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    marketCDF (twoAtomPop a ha0 ha1) continuousTwoAtomLoss (1/4) = a := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold marketCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if continuousTwoAtomLoss x ≤ 1/4 then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if continuousTwoAtomLoss (some y) ≤ 1/4 then 1 else 0)))
  rw [h, h2]
  have hnone : twoAtomProb a none = 0 := by simp [twoAtomProb]
  have hz0 : twoAtomProb a (some 0) = a := by simp [twoAtomProb]
  have hz1 : twoAtomProb a (some 1) = 1 - a := by simp [twoAtomProb]
  rw [hnone, hz0, hz1]
  have e0 : continuousTwoAtomLoss none = 0 := by simp [continuousTwoAtomLoss]
  have e1 : continuousTwoAtomLoss (some 0) = 0 := by simp [continuousTwoAtomLoss]
  have e2 : continuousTwoAtomLoss (some 1) = 1/2 := by simp [continuousTwoAtomLoss]
  rw [e0, e1, e2]
  have hl0 : ((0:ℝ) ≤ 1/4) := by norm_num
  have hnl1 : ¬ ((1/2:ℝ) ≤ 1/4) := by norm_num
  simp only [hl0, hnl1, if_true, if_false]
  ring

/-- At every threshold strictly below one half, the real-loss two-atom CDF is at most `a`. -/
theorem continuousTwoAtom_cdf_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {s : ℝ} (hs : s < 1/2) :
    marketCDF (twoAtomPop a ha0 ha1) continuousTwoAtomLoss s ≤ a := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold marketCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if continuousTwoAtomLoss x ≤ s then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if continuousTwoAtomLoss (some y) ≤ s then 1 else 0)))
  rw [h, h2]
  have hnone : twoAtomProb a none = 0 := by simp [twoAtomProb]
  have hz0 : twoAtomProb a (some 0) = a := by simp [twoAtomProb]
  have hz1 : twoAtomProb a (some 1) = 1 - a := by simp [twoAtomProb]
  rw [hnone, hz0, hz1]
  have e0 : continuousTwoAtomLoss none = 0 := by simp [continuousTwoAtomLoss]
  have e1 : continuousTwoAtomLoss (some 0) = 0 := by simp [continuousTwoAtomLoss]
  have e2 : continuousTwoAtomLoss (some 1) = 1/2 := by simp [continuousTwoAtomLoss]
  rw [e0, e1, e2]
  by_cases hs0 : ((0:ℝ) ≤ s)
  · by_cases hs1 : ((1/2:ℝ) ≤ s)
    · simp only [hs0, hs1, if_true]
      linarith [hs]
    · simp only [hs0, hs1, if_true, if_false]
      linarith [hs]
  · have hs1 : ¬ ((1/2:ℝ) ≤ s) := by linarith [hs]
    simp only [hs0, hs1, if_false]
    linarith
end Qatlib.Concepts.RiskEstimation.PopulationGap
