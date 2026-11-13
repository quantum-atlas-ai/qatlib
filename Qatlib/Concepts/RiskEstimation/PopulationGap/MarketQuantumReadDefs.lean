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
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitAccessDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ContinuousMarketCDFDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketQuantizationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketProgramResourcesDefs

/-!
# Loaded market CDF readout and error windows

This module compares exact threshold indicators with comparisons performed after dyadic loading.
Disagreement is confined to a narrow loss window, giving deterministic CDF loading error bounds
and probabilistic bounds that also include numerical preparation and sampling error. The
application is finite market risk readout as in [WoernerEgger2019].

Classical and Born weighted window regularity assumptions convert local window masses into
explicit precision terms. `marketHeadline_uniform` combines these terms on an entire finite
threshold grid, and the final results record sample and readout budgets.

## Main statements

* `marketIndicator_diff_le`: pointwise error is bounded by the window indicator.
* `marketQuantumJointBound`: sampling, preparation, and loading error at one threshold.
* `marketHeadline_uniform`: the finite grid failure probability bound.
* `marketHeadline_resources`: bounds on table reads and amplitude estimation records.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

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
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.RiskEstimation.PopulationGap (clause11 euclid_gcd_fuel)
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

/-- States that the loss lies strictly within distance `(1 / 2) ^ k` of threshold `t`. -/
def marketWindow {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) : Prop :=
  t - (1/2 : ℝ)^k < loss a ∧ loss a < t + (1/2 : ℝ)^k

/-- The indicator that the dyadically loaded loss is at most the dyadically loaded threshold. -/
noncomputable def marketLoadedIndicator {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) : ℝ :=
  if loadReal k (loss a) ≤ loadReal k t then 1 else 0

/-- The real valued indicator of `marketWindow`. -/
noncomputable def marketWindowIndicator {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) : ℝ :=
  if marketWindow loss k t a then 1 else 0

/-- The market window indicator is nonnegative. -/
theorem marketWindowIndicator_nonneg {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) : 0 ≤ marketWindowIndicator loss k t a := by
  unfold marketWindowIndicator
  split_ifs <;> norm_num

/-- Dyadic loading of `x` is strictly greater than `x - (1 / 2) ^ k`. -/
theorem loadReal_gt_sub {k : ℕ} (x : ℝ) : x - (1/2 : ℝ)^k < (loadReal k x : ℝ) := by
  have h := loadReal_error k x
  have h' : -(1/2 : ℝ)^k < (loadReal k x : ℝ) - x := (abs_lt.mp h).1
  linarith

/-- If loaded and exact threshold indicators disagree, the loss belongs to the loading error
window. -/
theorem marketWindow_of_decision_disagree {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ)
    (t : ℝ) (a : Option (Fin n))
    (hdisagree : marketLoadedIndicator loss k t a ≠ marketIndicator loss t a) :
    marketWindow loss k t a := by
  have hcast : ((loadReal k (loss a) : ℝ) ≤ (loadReal k t : ℝ)) ↔
      (loadReal k (loss a) ≤ loadReal k t) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  by_cases hlt : loadReal k (loss a) ≤ loadReal k t
  · by_cases hex : loss a ≤ t
    · have h1 : marketLoadedIndicator loss k t a = 1 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 1 := by
        simp [marketIndicator, hex]
      exact absurd (h1.trans h2.symm) hdisagree
    · have h1 : marketLoadedIndicator loss k t a = 1 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 0 := by
        simp [marketIndicator, hex]
      have hsub := loadReal_gt_sub (k := k) (loss a)
      have htle := loadReal_le k t
      have hle : (loadReal k (loss a) : ℝ) ≤ (loadReal k t : ℝ) := hcast.mpr hlt
      constructor
      · linarith
      · linarith
  · by_cases hex : loss a ≤ t
    · have h1 : marketLoadedIndicator loss k t a = 0 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 1 := by
        simp [marketIndicator, hex]
      have hq : loadReal k t < loadReal k (loss a) := lt_of_not_ge hlt
      have hr : (loadReal k t : ℝ) < (loadReal k (loss a) : ℝ) := by
        exact_mod_cast hq
      have hsub := loadReal_gt_sub (k := k) t
      have hle := loadReal_le k (loss a)
      constructor
      · linarith
      · linarith
    · have h1 : marketLoadedIndicator loss k t a = 0 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 0 := by
        simp [marketIndicator, hex]
      exact absurd (h1.trans h2.symm) hdisagree

/-- The absolute difference of loaded and exact threshold indicators is bounded by the window
indicator. -/
theorem marketIndicator_diff_le {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) :
    |marketLoadedIndicator loss k t a - marketIndicator loss t a|
      ≤ marketWindowIndicator loss k t a := by
  by_cases hlt : loadReal k (loss a) ≤ loadReal k t
  · by_cases hex : loss a ≤ t
    · have h1 : marketLoadedIndicator loss k t a = 1 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 1 := by
        simp [marketIndicator, hex]
      rw [h1, h2]
      simp only [sub_self, abs_zero]
      exact marketWindowIndicator_nonneg loss k t a
    · have h1 : marketLoadedIndicator loss k t a = 1 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 0 := by
        simp [marketIndicator, hex]
      have hw := marketWindow_of_decision_disagree loss k t a (by rw [h1, h2]; simp)
      have h3 : marketWindowIndicator loss k t a = 1 := by
        simp [marketWindowIndicator, hw]
      rw [h1, h2, h3]
      simp
  · by_cases hex : loss a ≤ t
    · have h1 : marketLoadedIndicator loss k t a = 0 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 1 := by
        simp [marketIndicator, hex]
      have hw := marketWindow_of_decision_disagree loss k t a (by rw [h1, h2]; simp)
      have h3 : marketWindowIndicator loss k t a = 1 := by
        simp [marketWindowIndicator, hw]
      rw [h1, h2, h3]
      simp
    · have h1 : marketLoadedIndicator loss k t a = 0 := by
        simp [marketLoadedIndicator, hlt]
      have h2 : marketIndicator loss t a = 0 := by
        simp [marketIndicator, hex]
      rw [h1, h2]
      simp only [sub_self, abs_zero]
      exact marketWindowIndicator_nonneg loss k t a

/-- The exact loss threshold indicator summed against the Born weights of `A *ᵥ Ket j`. -/
noncomputable def marketQuantumCDF {n : ℕ} (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ)
    (j : Option (Fin n)) (loss : Option (Fin n) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i

/-- The loaded loss threshold indicator summed against the Born weights of `A *ᵥ Ket j`. -/
noncomputable def marketQuantumLoadedCDF {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i

/-- The loading error window indicator summed against the Born weights of `A *ᵥ Ket j`. -/
noncomputable def marketQuantumWindowMass {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketWindowIndicator loss k t i

/-- The loaded loss threshold indicator averaged under a finite probability distribution. -/
noncomputable def marketLoadedCDF {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ a, p.prob a * marketLoadedIndicator loss k t a

/-- The loaded classical CDF differs from the exact CDF by at most the probability mass of the
loading error window. -/
theorem marketLoadedCDF_deviation {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) :
    |marketLoadedCDF p loss k t - marketCDF p loss t|
      ≤ ∑ a, p.prob a * marketWindowIndicator loss k t a := by
  have hrewrite : marketLoadedCDF p loss k t - marketCDF p loss t
      = ∑ a, (p.prob a * marketLoadedIndicator loss k t a
        - p.prob a * marketIndicator loss t a) := by
    have h1 : marketLoadedCDF p loss k t
        = ∑ a, p.prob a * marketLoadedIndicator loss k t a := rfl
    have h2 : marketCDF p loss t = ∑ a, p.prob a * marketIndicator loss t a := rfl
    rw [h1, h2]
    exact (Finset.sum_sub_distrib
      (fun a => p.prob a * marketLoadedIndicator loss k t a)
      (fun a => p.prob a * marketIndicator loss t a)).symm
  have hsum : |∑ a, (p.prob a * marketLoadedIndicator loss k t a
        - p.prob a * marketIndicator loss t a)|
      ≤ ∑ a, |p.prob a * marketLoadedIndicator loss k t a
        - p.prob a * marketIndicator loss t a| := by
    have h := Finset.abs_sum_le_sum_abs
      (fun a => p.prob a * marketLoadedIndicator loss k t a - p.prob a * marketIndicator loss t a)
      (Finset.univ : Finset (Option (Fin n)))
    simpa using! h
  rw [hrewrite]
  calc |∑ a, (p.prob a * marketLoadedIndicator loss k t a
        - p.prob a * marketIndicator loss t a)|
      ≤ ∑ a, |p.prob a * marketLoadedIndicator loss k t a
        - p.prob a * marketIndicator loss t a| := hsum
    _ = ∑ a, p.prob a * |marketLoadedIndicator loss k t a - marketIndicator loss t a| := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← mul_sub, abs_mul, abs_of_nonneg (p.nonneg a)]
    _ ≤ ∑ a, p.prob a * marketWindowIndicator loss k t a := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (marketIndicator_diff_le loss k t a) (p.nonneg a)

/-- The loaded Born weighted CDF differs from its exact counterpart by at most
`marketQuantumWindowMass`. -/
theorem marketQuantumLoadedCDF_deviation {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) :
    |marketQuantumLoadedCDF A j loss k t - marketQuantumCDF A j loss t|
      ≤ marketQuantumWindowMass A j loss k t := by
  have hrewrite : marketQuantumLoadedCDF A j loss k t - marketQuantumCDF A j loss t
      = ∑ i, (BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i) := by
    have h1 : marketQuantumLoadedCDF A j loss k t
        = ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i := rfl
    have h2 : marketQuantumCDF A j loss t
        = ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i := rfl
    rw [h1, h2]
    exact (Finset.sum_sub_distrib
      (fun i => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i)
      (fun i => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i)).symm
  have hsum : |∑ i, (BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i)|
      ≤ ∑ i, |BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i| := by
    have h := Finset.abs_sum_le_sum_abs
      (fun i => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i)
      (Finset.univ : Finset (Option (Fin n)))
    simpa using! h
  rw [hrewrite]
  calc |∑ i, (BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i)|
      ≤ ∑ i, |BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketLoadedIndicator loss k t i
        - BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketIndicator loss t i| := hsum
    _ = ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i
        * |marketLoadedIndicator loss k t i - marketIndicator loss t i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_sub, abs_mul, abs_of_nonneg (bornProb_nonneg _ _)]
    _ ≤ ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * marketWindowIndicator loss k t i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (marketIndicator_diff_le loss k t i)
          (bornProb_nonneg _ _)
    _ = marketQuantumWindowMass A j loss k t := rfl

/-- The Born weighted market CDF is monotone in its threshold. -/
theorem marketQuantumCDF_monotone {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) :
    Monotone (marketQuantumCDF A j loss) := by
  intro a b hab
  unfold marketQuantumCDF
  apply Finset.sum_le_sum
  intro i hi
  by_cases hia : loss i ≤ a
  · have hib : loss i ≤ b := le_trans hia hab
    simp [marketIndicator, hia, hib]
  · by_cases hib : loss i ≤ b
    · have h1 : marketIndicator loss a i = 0 := by simp [marketIndicator, hia]
      have h2 : marketIndicator loss b i = 1 := by simp [marketIndicator, hib]
      simp only [h1, h2]
      have hb := bornProb_nonneg (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i
      linarith
    · simp [marketIndicator, hia, hib]

/-- Requires every ordered Born weighted CDF increment to be at most `ρ` times the threshold
increment. -/
def marketQuantumCDFLipschitz {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → marketQuantumCDF A j loss b - marketQuantumCDF A j loss a
    ≤ ρ * (b - a)

/-- The exact market threshold indicator is nonnegative. -/
theorem marketIndicator_nonneg {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : 0 ≤ marketIndicator loss t a := by
  unfold marketIndicator
  split_ifs <;> norm_num

/-- The market threshold indicator is zero exactly when the loss is not at most the threshold. -/
theorem marketIndicator_eq_zero_iff {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : marketIndicator loss t a = 0 ↔ ¬ (loss a ≤ t) := by
  unfold marketIndicator
  by_cases h : loss a ≤ t <;> simp [h]

/-- The market threshold indicator is one exactly when the loss is at most the threshold. -/
theorem marketIndicator_eq_one_iff {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : marketIndicator loss t a = 1 ↔ loss a ≤ t := by
  unfold marketIndicator
  by_cases h : loss a ≤ t <;> simp [h]

/-- The rational valued indicator that the loss is at most the threshold. -/
noncomputable def marketIndicatorQ {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : ℚ := if loss a ≤ t then 1 else 0

/-- Casting the rational threshold indicator to the reals gives the real threshold indicator. -/
theorem marketIndicatorQ_cast {n : ℕ} (loss : Option (Fin n) → ℝ) (t : ℝ)
    (a : Option (Fin n)) : (marketIndicatorQ loss t a : ℝ) = marketIndicator loss t a := by
  unfold marketIndicatorQ marketIndicator
  split_ifs <;> norm_num

/-- The rational threshold indicator summed with empirical multiplicities equals its sum over
the sample records. -/
theorem marketCountIndicatorQ {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) :
    (∑ a, (empiricalWeight ω a : ℚ) * marketIndicatorQ loss t a)
      = (∑ k : Fin N, marketIndicatorQ loss t (ω k) : ℚ) := by
  have h := empirical_indicator_sum (List.ofFn ω) (fun a => loss a ≤ t)
  have hlist (xs : List (Option (Fin n))) :
      (xs.filter (fun a => decide (loss a ≤ t))).length
        = (xs.map (fun a => marketIndicatorQ loss t a)).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih => by_cases h : loss a ≤ t <;> simp [h, ih, add_comm, marketIndicatorQ]
  have hsimpa : (∑ a, (empiricalWeight ω a : ℚ) * marketIndicatorQ loss t a)
      = ∑ a, ((List.ofFn ω).count a : ℚ) * (if loss a ≤ t then (1 : ℚ) else 0) := by
    simp only [empiricalWeight, marketIndicatorQ]
  rw [hsimpa, h]
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

/-- The real threshold indicator summed with empirical multiplicities equals its sum over the
sample records. -/
theorem marketCountIndicator {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) :
    (∑ a, ((empiricalWeight ω a : ℚ) : ℝ) * marketIndicator loss t a)
      = ∑ k : Fin N, marketIndicator loss t (ω k) := by
  have hq := marketCountIndicatorQ ω loss t
  have h1 : (∑ a, ((empiricalWeight ω a : ℚ) : ℝ)
        * ((marketIndicatorQ loss t a : ℚ) : ℝ))
      = (((∑ a, (empiricalWeight ω a : ℚ) * marketIndicatorQ loss t a) : ℚ) : ℝ) := by
    push_cast
    rfl
  have h2 : (((∑ a, (empiricalWeight ω a : ℚ) * marketIndicatorQ loss t a) : ℚ) : ℝ)
      = (((∑ k : Fin N, marketIndicatorQ loss t (ω k)) : ℚ) : ℝ) := by
    rw [hq]
  have h2' : (((∑ k : Fin N, marketIndicatorQ loss t (ω k)) : ℚ) : ℝ)
      = ∑ k : Fin N, ((marketIndicatorQ loss t (ω k) : ℚ) : ℝ) := by
    push_cast
    rfl
  have h3 : (∑ k : Fin N, ((marketIndicatorQ loss t (ω k) : ℚ) : ℝ))
      = ∑ k : Fin N, marketIndicator loss t (ω k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [marketIndicatorQ_cast]
  calc
    (∑ a, ((empiricalWeight ω a : ℚ) : ℝ) * marketIndicator loss t a)
        = ∑ a, ((empiricalWeight ω a : ℚ) : ℝ)
            * ((marketIndicatorQ loss t a : ℚ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [marketIndicatorQ_cast]
    _ = ∑ k : Fin N, ((marketIndicatorQ loss t (ω k) : ℚ) : ℝ) := by
          calc
            (∑ a, ((empiricalWeight ω a : ℚ) : ℝ)
                * ((marketIndicatorQ loss t a : ℚ) : ℝ))
                = (((∑ a, (empiricalWeight ω a : ℚ) * marketIndicatorQ loss t a) : ℚ) : ℝ) := h1
            _ = (((∑ k : Fin N, marketIndicatorQ loss t (ω k)) : ℚ) : ℝ) := h2
            _ = ∑ k : Fin N, ((marketIndicatorQ loss t (ω k) : ℚ) : ℝ) := h2'
    _ = ∑ k : Fin N, marketIndicator loss t (ω k) := h3

/-- For positive sample size, ideal empirical weight preparation gives threshold expectation
equal to the empirical CDF. -/
theorem marketIdealPayoff_eq_empiricalCDF {n N : ℕ} (ω : Fin N → Option (Fin n))
    (hN : 0 < N) (loss : Option (Fin n) → ℝ) (t : ℝ) :
    (∑ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) a
      * marketIndicator loss t a) = marketEmpiricalCDF ω loss t := by
  have hborn : ∀ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) a
      = (empiricalWeight ω a / N : ℚ) := fun a => empirical_ideal_born ω hN a
  calc
    (∑ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) a
        * marketIndicator loss t a)
      = ∑ a, ((empiricalWeight ω a / N : ℚ) : ℝ) * marketIndicator loss t a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hborn a]
    _ = ∑ a, ((empiricalWeight ω a : ℚ) : ℝ) * marketIndicator loss t a / (N : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [empiricalWeight]
        push_cast
        ring
    _ = (∑ a, ((empiricalWeight ω a : ℚ) : ℝ) * marketIndicator loss t a)
        / (N : ℝ) := by
        rw [← Finset.sum_div]
    _ = (∑ k : Fin N, marketIndicator loss t (ω k)) / (N : ℝ) := by
        rw [marketCountIndicator]
    _ = marketEmpiricalCDF ω loss t := rfl

/-- For positive sample size, numerical empirical preparation changes the threshold expectation
by at most `64 * n / 2 ^ bits`. -/
theorem marketQuantumPrepBias {n N bits : ℕ} (ω : Fin N → Option (Fin n))
    (hN : 0 < N) (loss : Option (Fin n) → ℝ) (t : ℝ) :
    |marketQuantumCDF (empiricalPrepare ω bits) none loss t - marketEmpiricalCDF ω loss t|
      ≤ 64*(n : ℝ)/2^bits := by
  have hbias := empirical_prepare_payoff_bias ω bits hN (marketIndicator loss t)
    (fun a => ⟨marketIndicator_nonneg loss t a, marketIndicator_le_one loss t a⟩)
  have hleft : (∑ a, BornProb ((empiricalPrepare ω bits) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) a
      * marketIndicator loss t a) = marketQuantumCDF (empiricalPrepare ω bits) none loss t := rfl
  have hright : (∑ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) a
      * marketIndicator loss t a) = marketEmpiricalCDF ω loss t :=
    marketIdealPayoff_eq_empiricalCDF ω hN loss t
  rw [← hleft, ← hright]
  exact hbias

/-- Inclusion of sample record events implies the corresponding ordering of their probabilities. -/
theorem marketProbEvent_mono {n N : ℕ} (p : FinDist (Option (Fin n)))
    (E F : (Fin N → Option (Fin n)) → Prop) [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) :
    FinDist.probEvent (L := N) p E ≤ FinDist.probEvent (L := N) p F := by
  have hprobOf_nonneg : ∀ ω : Fin N → Option (Fin n), 0 ≤ p.probOf ω := by
    intro ω
    unfold FinDist.probOf
    exact Finset.prod_nonneg fun i _ => p.nonneg (ω i)
  unfold FinDist.probEvent
  have hsub : Finset.univ.filter E ⊆ Finset.univ.filter F := by
    intro ω hω
    have hmemE : E ω := (Finset.mem_filter.mp hω).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEF ω hmemE⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hprobOf_nonneg ω)

/-- The probability that loaded quantum CDF error exceeds sampling tolerance plus preparation
bias and window mass is at most `1 / (4 * N * ν ^ 2)`. -/
theorem marketQuantumJointBound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (bits k : ℕ) (loss : Option (Fin n) → ℝ) (t : ℝ) (ν : ℝ)
    (hN : 0 < N) (hν : 0 < ν) :
    FinDist.probEvent (L := N) p
      (fun ω : Fin N → Option (Fin n) =>
        ν + 64*(n : ℝ)/2^bits
          + marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t
          < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
              - marketCDF p loss t|)
      ≤ 1/(4*(N : ℝ)*ν^2) := by
  have hpoint (ω : Fin N → Option (Fin n)) :
      |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t - marketCDF p loss t|
        ≤ marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t
          + 64*(n : ℝ)/2^bits
          + |marketEmpiricalCDF ω loss t - marketCDF p loss t| := by
    have h1 := marketQuantumLoadedCDF_deviation (empiricalPrepare ω bits) none loss k t
    have h3 := marketQuantumPrepBias (bits := bits) ω hN loss t
    have h4 : |marketQuantumCDF (empiricalPrepare ω bits) none loss t - marketCDF p loss t|
        ≤ 64*(n : ℝ)/2^bits + |marketEmpiricalCDF ω loss t - marketCDF p loss t| := by
      have hsub := abs_sub_le (marketQuantumCDF (empiricalPrepare ω bits) none loss t)
        (marketEmpiricalCDF ω loss t) (marketCDF p loss t)
      linarith
    calc
      |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
          - marketCDF p loss t|
          ≤ |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
                - marketQuantumCDF (empiricalPrepare ω bits) none loss t|
            + |marketQuantumCDF (empiricalPrepare ω bits) none loss t
                - marketCDF p loss t| :=
          abs_sub_le _ _ _
      _ ≤ |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
                - marketQuantumCDF (empiricalPrepare ω bits) none loss t|
            + (64*(n : ℝ)/2^bits
                + |marketEmpiricalCDF ω loss t - marketCDF p loss t|) := by
          linarith
      _ ≤ marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t
            + 64*(n : ℝ)/2^bits
            + |marketEmpiricalCDF ω loss t - marketCDF p loss t| := by
          linarith
  have hsub : ∀ ω : Fin N → Option (Fin n),
      (ν + 64*(n : ℝ)/2^bits
          + marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t
          < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
              - marketCDF p loss t|)
        → (ν < |marketEmpiricalCDF ω loss t - marketCDF p loss t|) := by
    intro ω hω
    have hp := hpoint ω
    linarith
  have hmono := marketProbEvent_mono p
    (fun ω : Fin N → Option (Fin n) =>
      ν + 64*(n : ℝ)/2^bits
        + marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t
        < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
            - marketCDF p loss t|)
    (fun ω : Fin N → Option (Fin n) =>
      ν < |marketEmpiricalCDF ω loss t - marketCDF p loss t|) hsub
  exact hmono.trans (marketCDF_sampling_bound p loss t ν hN hν)

/-- The weighted indicator difference between thresholds `t + (1 / 2) ^ k` and `t - (1 / 2) ^
k`. -/
noncomputable def marketBandDiff {n : ℕ} (w : Option (Fin n) → ℝ) (loss : Option (Fin n) → ℝ)
    (k : ℕ) (t : ℝ) : ℝ :=
  ∑ a, w a * ((if loss a ≤ t + (1/2 : ℝ)^k then (1 : ℝ) else 0)
    - (if loss a ≤ t - (1/2 : ℝ)^k then (1 : ℝ) else 0))

/-- The open window indicator is bounded by the difference of the indicators at its upper and
lower endpoints. -/
theorem marketWindowIndicator_le_band {n : ℕ} (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ)
    (a : Option (Fin n)) :
    marketWindowIndicator loss k t a
      ≤ (if loss a ≤ t + (1/2 : ℝ)^k then (1 : ℝ) else 0)
        - (if loss a ≤ t - (1/2 : ℝ)^k then (1 : ℝ) else 0) := by
  have hδ : 0 ≤ (1/2 : ℝ)^k := by positivity
  by_cases hw : marketWindow loss k t a
  · have h1 : loss a ≤ t + (1/2 : ℝ)^k := by
      rcases hw with ⟨h1, h2⟩
      linarith
    have h2 : ¬ (loss a ≤ t - (1/2 : ℝ)^k) := by
      rcases hw with ⟨h1, h2⟩
      linarith
    rw [marketWindowIndicator, if_pos hw, if_pos h1, if_neg h2]
    norm_num
  · rw [marketWindowIndicator, if_neg hw]
    by_cases h1 : loss a ≤ t + (1/2 : ℝ)^k
    · by_cases h2 : loss a ≤ t - (1/2 : ℝ)^k
      · rw [if_pos h1, if_pos h2]
        norm_num
      · rw [if_pos h1, if_neg h2]
        norm_num
    · by_cases h2 : loss a ≤ t - (1/2 : ℝ)^k
      · exfalso
        have h3 : loss a ≤ t + (1/2 : ℝ)^k := by linarith
        exact h1 h3
      · rw [if_neg h1, if_neg h2]
        norm_num

/-- With probability weights, the band difference equals the population CDF increment across the
band. -/
theorem marketBandDiff_eq {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) :
    marketBandDiff p.prob loss k t
      = marketCDF p loss (t + (1/2 : ℝ)^k) - marketCDF p loss (t - (1/2 : ℝ)^k) := by
  unfold marketBandDiff marketCDF
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- With Born weights, the band difference equals the quantum CDF increment across the band. -/
theorem marketBandDiff_eq_quantum {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (k : ℕ) (t : ℝ) :
    marketBandDiff (fun a => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) a) loss k t
      = marketQuantumCDF A j loss (t + (1/2 : ℝ)^k)
        - marketQuantumCDF A j loss (t - (1/2 : ℝ)^k) := by
  unfold marketBandDiff marketQuantumCDF marketIndicator
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Requires the classical loading window mass at every threshold to be at most `ρ * 2 * (1 / 2)
^ k`. -/
def marketWindowRegular {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ) : Prop :=
  ∀ t : ℝ, (∑ a, p.prob a * marketWindowIndicator loss k t a) ≤ ρ * 2 * (1/2 : ℝ)^k

/-- Requires the Born weighted loading window mass at every threshold to be at most `ρ * 2 * (1
/ 2) ^ k`. -/
def marketQuantumWindowRegular {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ) : Prop :=
  ∀ t : ℝ, marketQuantumWindowMass A j loss k t ≤ ρ * 2 * (1/2 : ℝ)^k

/-- CDF regularity bounds the classical loading window mass by `ρ * 2 * (1 / 2) ^ k`. -/
theorem marketWindowMass_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ) (t : ℝ)
    (hLip : marketCDFLipschitz p loss ρ) :
    (∑ a, p.prob a * marketWindowIndicator loss k t a) ≤ ρ * 2 * (1/2 : ℝ)^k := by
  have hδ : 0 ≤ (1/2 : ℝ)^k := by positivity
  have hsum : (∑ a, p.prob a * marketWindowIndicator loss k t a)
      ≤ marketBandDiff p.prob loss k t := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (marketWindowIndicator_le_band loss k t a) (p.nonneg a)
  calc
    (∑ a, p.prob a * marketWindowIndicator loss k t a)
        ≤ marketBandDiff p.prob loss k t := hsum
    _ = marketCDF p loss (t + (1/2 : ℝ)^k) - marketCDF p loss (t - (1/2 : ℝ)^k) :=
          marketBandDiff_eq p loss k t
    _ ≤ ρ * ((t + (1/2 : ℝ)^k) - (t - (1/2 : ℝ)^k)) :=
          hLip (t - (1/2 : ℝ)^k) (t + (1/2 : ℝ)^k) (by linarith)
    _ = ρ * 2 * (1/2 : ℝ)^k := by ring

/-- Quantum CDF regularity bounds the Born weighted loading window mass by `ρ * 2 * (1 / 2) ^
k`. -/
theorem marketQuantumWindowMass_le {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ) (t : ℝ)
    (hLip : marketQuantumCDFLipschitz A j loss ρ) :
    marketQuantumWindowMass A j loss k t ≤ ρ * 2 * (1/2 : ℝ)^k := by
  have hδ : 0 ≤ (1/2 : ℝ)^k := by positivity
  have hsum : marketQuantumWindowMass A j loss k t
      ≤ marketBandDiff (fun a => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) a) loss k t := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (marketWindowIndicator_le_band loss k t a)
      (bornProb_nonneg _ _)
  calc
    marketQuantumWindowMass A j loss k t
        ≤ marketBandDiff (fun a => BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) a) loss k t := hsum
    _ = marketQuantumCDF A j loss (t + (1/2 : ℝ)^k)
        - marketQuantumCDF A j loss (t - (1/2 : ℝ)^k) :=
          marketBandDiff_eq_quantum A j loss k t
    _ ≤ ρ * ((t + (1/2 : ℝ)^k) - (t - (1/2 : ℝ)^k)) :=
          hLip (t - (1/2 : ℝ)^k) (t + (1/2 : ℝ)^k) (by linarith)
    _ = ρ * 2 * (1/2 : ℝ)^k := by ring

/-- The classical CDF regularity condition implies the loading window regularity condition. -/
theorem marketWindowRegular_of_lipschitz {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ)
    (hLip : marketCDFLipschitz p loss ρ) :
    marketWindowRegular p loss ρ k := by
  intro t
  exact marketWindowMass_le p loss ρ k t hLip

/-- The quantum CDF regularity condition implies the Born weighted loading window regularity
condition. -/
theorem marketQuantumWindowRegular_of_lipschitz {n : ℕ}
    (A : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ)
    (hLip : marketQuantumCDFLipschitz A j loss ρ) :
    marketQuantumWindowRegular A j loss ρ k := by
  intro t
  exact marketQuantumWindowMass_le A j loss ρ k t hLip

/-- Under uniform Born window regularity, the probability of any grid CDF error exceeding
loading, preparation, and sampling terms is at most `(iT + 1) / (4 * N * ν ^ 2)`. -/
theorem marketHeadline_uniform {n N : ℕ} (p : FinDist (Option (Fin n)))
    (bits k : ℕ) (loss : Option (Fin n) → ℝ) (ρ : ℝ) (Δ : ℝ) (iT : ℕ) (ν : ℝ)
    (hN : 0 < N) (hν : 0 < ν) (hρ : 0 ≤ ρ)
    (hRegQ : ∀ ω : Fin N → Option (Fin n),
      marketQuantumWindowRegular (empiricalPrepare ω bits) none loss ρ k) :
    FinDist.probEvent (L := N) p
      (fun ω : Fin N → Option (Fin n) =>
        ∃ i : Fin (iT+1),
          ρ * 2 * (1/2 : ℝ)^k + 64*(n : ℝ)/2^bits + ν
            < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k
                  (gridThreshold Δ i.1) - marketCDF p loss (gridThreshold Δ i.1)|)
      ≤ (iT + 1) / (4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin (iT+1) → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    ρ * 2 * (1/2 : ℝ)^k + 64*(n : ℝ)/2^bits + ν
      < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k (gridThreshold Δ i.1)
          - marketCDF p loss (gridThreshold Δ i.1)|
  have hE : ∀ i : Fin (iT+1),
      FinDist.probEvent (L := N) p (E i) ≤ 1/(4*(N : ℝ)*ν^2) := by
    intro i
    have hwin : ∀ ω : Fin N → Option (Fin n),
        marketQuantumWindowMass (empiricalPrepare ω bits) none loss k (gridThreshold Δ i.1)
          ≤ ρ * 2 * (1/2 : ℝ)^k := by
      intro ω
      exact (hRegQ ω) (gridThreshold Δ i.1)
    have hmono : ∀ ω : Fin N → Option (Fin n), E i ω →
        (ν + 64*(n : ℝ)/2^bits
          + marketQuantumWindowMass (empiricalPrepare ω bits) none loss k
              (gridThreshold Δ i.1)
          < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k
              (gridThreshold Δ i.1) - marketCDF p loss (gridThreshold Δ i.1)|) := by
      intro ω hω
      have hw := hwin ω
      have herr : 0 ≤ ρ * 2 * (1/2 : ℝ)^k + 64*(n : ℝ)/2^bits + ν := by
        have hρ2 : 0 ≤ ρ * 2 * (1/2 : ℝ)^k := by positivity
        have hn2 : 0 ≤ 64*(n : ℝ)/2^bits := by positivity
        have hν2 : 0 ≤ ν := le_of_lt hν
        linarith
      linarith
    have hmono2 := marketProbEvent_mono p (E i)
      (fun ω : Fin N → Option (Fin n) =>
        ν + 64*(n : ℝ)/2^bits
          + marketQuantumWindowMass (empiricalPrepare ω bits) none loss k
              (gridThreshold Δ i.1)
          < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k
              (gridThreshold Δ i.1) - marketCDF p loss (gridThreshold Δ i.1)|) hmono
    exact hmono2.trans (marketQuantumJointBound p bits k loss (gridThreshold Δ i.1) ν hN hν)
  have h := p.union_bound (L := N) (M := iT+1) E
  have hs : FinDist.probEvent (L := N) p
      (fun ω : Fin N → Option (Fin n) =>
        ∃ i : Fin (iT+1),
          ρ * 2 * (1/2 : ℝ)^k + 64*(n : ℝ)/2^bits + ν
            < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k
                  (gridThreshold Δ i.1) - marketCDF p loss (gridThreshold Δ i.1)|)
      = FinDist.probEvent (L := N) p (fun ω => ∃ i, E i ω) := by
    unfold FinDist.probEvent
    congr 1
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin (iT+1), FinDist.probEvent (L := N) p (E i))
      ≤ ∑ i : Fin (iT+1), 1/(4*(N : ℝ)*ν^2) :=
      Finset.sum_le_sum (fun i _ => hE i)
    _ = (iT + 1) / (4*(N : ℝ)*ν^2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- Window regularity bounds the classical loaded CDF error by `ρ * 2 * (1 / 2) ^ k`. -/
theorem marketLoadedCDF_deviation_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ) (t : ℝ)
    (hReg : marketWindowRegular p loss ρ k) :
    |marketLoadedCDF p loss k t - marketCDF p loss t| ≤ ρ * 2 * (1/2 : ℝ)^k := by
  calc
    |marketLoadedCDF p loss k t - marketCDF p loss t|
        ≤ ∑ a, p.prob a * marketWindowIndicator loss k t a :=
          marketLoadedCDF_deviation p loss k t
    _ ≤ ρ * 2 * (1/2 : ℝ)^k := hReg t

/-- CDF regularity bounds the classical loaded CDF error by `ρ * 2 * (1 / 2) ^ k`. -/
theorem marketLoadedCDF_deviation_le_of_lipschitz {n : ℕ}
    (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℝ) (ρ : ℝ) (k : ℕ)
    (t : ℝ) (hLip : marketCDFLipschitz p loss ρ) :
    |marketLoadedCDF p loss k t - marketCDF p loss t| ≤ ρ * 2 * (1/2 : ℝ)^k := by
  exact marketLoadedCDF_deviation_le p loss ρ k t (marketWindowRegular_of_lipschitz p loss ρ k hLip)

/-- For positive parameters, a grid failure bound at most `δ` implies `N ≥ (iT + 1) / (4 * δ * ν
^ 2)`. -/
theorem marketHeadline_sampling_budget {iT : ℕ} {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (N : ℕ) (hN : 0 < N) (hbound : (iT + 1) / (4*(N : ℝ)*ν^2) ≤ δ) :
    (iT + 1) / (4*δ*ν^2) ≤ (N : ℝ) := by
  have hδν : 0 < 4*δ*ν^2 := by
    have h1 : 0 < δ * ν^2 := mul_pos hδ (sq_pos_of_pos hν)
    nlinarith
  have hNν : 0 < 4*(N : ℝ)*ν^2 := by
    have h1 : 0 < (N : ℝ) * ν^2 := mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hν)
    nlinarith
  have hmul : (iT + 1) ≤ δ * (4*(N : ℝ)*ν^2) := by
    have h := (div_le_iff₀ hNν).mp hbound
    linarith
  have hdiv : (iT + 1) / (4*δ*ν^2) ≤ δ * (4*(N : ℝ)*ν^2) / (4*δ*ν^2) :=
    div_le_div_of_nonneg_right hmul (le_of_lt hδν)
  calc
    (iT + 1) / (4*δ*ν^2) ≤ δ * (4*(N : ℝ)*ν^2) / (4*δ*ν^2) := hdiv
    _ = (N : ℝ) := by field_simp

/-- The grid failure bound implies the corresponding ceiling lower bound on sample size. -/
theorem marketHeadline_sampling_budget_ceil {iT : ℕ} {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (N : ℕ) (hN : 0 < N) (hbound : (iT + 1) / (4*(N : ℝ)*ν^2) ≤ δ) :
    Nat.ceil ((iT + 1) / (4*δ*ν^2)) ≤ N := by
  have h := marketHeadline_sampling_budget hδ hν N hN hbound
  exact Nat.ceil_le.mpr h

/-- The table read count is at most `iT + 1`, and the amplitude estimation record count is at
most `(iT + 1) * (2 * r + 1)`. -/
theorem marketHeadline_resources {n N : ℕ} (M r : ℕ) (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).tableReads ≤ iT + 1 ∧
    (marketProgramResources M r ω loss Δ q iT).aeRecords
      ≤ (iT + 1) * (2*r+1) := by
  refine ⟨marketGridScan_le ω loss Δ q iT, ?_⟩
  rw [marketProgramResources_ae, marketProgramResources_reads]
  exact Nat.mul_le_mul_right (2*r+1) (marketGridScan_le ω loss Δ q iT)
end Qatlib.Concepts.RiskEstimation.PopulationGap
