/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative

/-!
# Product sampling and statistics of POVM records

`povmSampleLaw` equips finite POVM outcome records with their product distribution. The module
proves unbiasedness and variance identities for reconstructed sample means, bounds variance by
`povmMomentEffect`, and obtains confidence bounds for one or two reconstructed observables;
[Holevo1982] provides the quantum statistical background.

It also defines `povmUStatisticK` as an average over ordered tuples of distinct positions and
proves its unbiasedness. Additional results establish counted rational insertion-sort properties
and specify an axis selector driven by outcome labels.

## Main statements

* `povm_sample_mean_unbiased` and `povm_sample_mean_variance`: expectation and mean squared
  error.
* `povm_sample_confidence_bound`: a moment-effect confidence bound.
* `povmUStatisticK_unbiased`: unbiased averaging over distinct tuples.
* `rationalInsertionSortCounted_median_property`: inequalities around the sorted median.
* `nativeResultDependentAxis_append`: the axis-selector update after one record.

## References

* [Holevo, 1982][Holevo1982]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasuredStatistics

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- The product distribution of `n` independent outcomes drawn from the POVM record law of the
density operator `ρ`. -/
noncomputable def povmSampleLaw (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} : FinDist (Fin n → O) where
  prob ω := (povmRecordLaw E ρ hρ).probOf ω
  nonneg ω := Finset.prod_nonneg fun i _ => (povmRecordLaw E ρ hρ).nonneg _
  sum_one := (povmRecordLaw E ρ hρ).sum_probOf n

/-- The probability of a sample record under `povmSampleLaw` is its product probability under
`povmRecordLaw`. -/
theorem povmSampleLaw_prob (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (ω : Fin n → O) :
    (povmSampleLaw E ρ hρ).prob ω = (povmRecordLaw E ρ hρ).probOf ω := rfl

/-- The expectation of an event indicator under `povmSampleLaw` equals its product-law event
probability. -/
theorem povmSampleLaw_event (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (Ev : (Fin n → O) → Prop) [DecidablePred Ev] :
    (povmSampleLaw E ρ hρ).expect (fun ω : Fin n → O => if Ev ω then 1 else 0)
      = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ) Ev := by
  show (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
      * (if Ev ω then 1 else 0)) = _
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun ω _ => by rw [mul_ite, mul_one, mul_zero]

/-- For a POVM with bijective measurement map and a positive sample size, the reconstructed
sample mean has expectation equal to the real part of `trace (A * ρ)`. -/
theorem povm_sample_mean_unbiased (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) {n : ℕ} (hn : 0 < n) :
    (povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM A) ω)
      = (Matrix.trace (A * ρ)).re := by
  have h1 :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_avg (povmRecordLaw E ρ hρ)
      (povmStatistic E hM A) hn
  rw [povm_expect_statistic E hM ρ hρ A] at h1
  exact h1

/-- The mean squared error of the reconstructed sample mean is the single-record variance
divided by the positive sample size `n`. -/
theorem povm_sample_mean_variance (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) {n : ℕ} (hn : 0 < n) :
    (povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O => (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM A) ω
          - (Matrix.trace (A * ρ)).re) ^ 2)
      = (povmRecordLaw E ρ hρ).variance (povmStatistic E hM A) / n := by
  have h1 := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_avg_sub_sq (povmRecordLaw E ρ hρ)
    (povmStatistic E hM A) hn
  rw [povm_expect_statistic E hM ρ hρ A] at h1
  exact h1

/-- The POVM moment effect associated with the reconstructed statistic is positive semidefinite. -/
theorem povmMomentEffect_posSemidef (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (A : Operator D) :
    (povmMomentEffect E hM A).PosSemidef := by
  rw [povmMomentEffect]
  refine Matrix.posSemidef_sum Finset.univ fun o _ => ?_
  have hc : (0 : ℂ) ≤ ((povmStatistic E hM A o) ^ 2 : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact RCLike.ofReal_nonneg.mpr (sq_nonneg (povmStatistic E hM A o))
  exact Matrix.PosSemidef.smul (FinitePOVM.effect_posSemidef E o) hc

/-- The variance of the reconstructed POVM statistic is bounded by the norm of its moment
effect. -/
theorem povm_variance_le (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (povmRecordLaw E ρ hρ).variance (povmStatistic E hM A)
      ≤ ‖povmMomentEffect E hM A‖ := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h1
    · subst h0
      exact absurd (hρ.2.symm.trans (Matrix.trace_eq_zero_of_isEmpty ρ)) (by simp)
    · exact h1
  have hcenter := Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinDist.expect_centered_sq (povmRecordLaw E ρ hρ)
    (povmStatistic E hM A)
  have hsecond := povm_expect_statistic_sq E hM ρ hρ A
  have hpsd := povmMomentEffect_posSemidef E hM A
  have htrace := re_trace_psd_density_le hpsd.1 hpsd hρ hD
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance
  rw [hcenter, hsecond, povm_expect_statistic E hM ρ hρ A]
  calc (Matrix.trace (povmMomentEffect E hM A * ρ)).re
        - (Matrix.trace (A * ρ)).re ^ 2
      ≤ (Matrix.trace (povmMomentEffect E hM A * ρ)).re :=
        sub_le_self _ (sq_nonneg (Matrix.trace (A * ρ)).re)
    _ ≤ ‖povmMomentEffect E hM A‖ := htrace

/-- For positive `n` and `ε`, the probability that the reconstructed sample mean deviates by
more than `ε` is bounded by the single-record variance divided by `n * ε ^ 2`. -/
theorem povm_sample_confidence (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM A) ω
          - (Matrix.trace (A * ρ)).re|)
      ≤ (povmRecordLaw E ρ hρ).variance (povmStatistic E hM A) / (n * ε ^ 2) := by
  have h1 := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.chebyshev_avg (povmRecordLaw E ρ hρ)
    (povmStatistic E hM A) hn ε hε
  rw [povm_expect_statistic E hM ρ hρ A] at h1
  exact h1

/-- For positive `n` and `ε`, the sample-mean deviation probability is bounded by the
moment-effect norm divided by `n * ε ^ 2`. -/
theorem povm_sample_confidence_bound (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM A) ω
          - (Matrix.trace (A * ρ)).re|)
      ≤ ‖povmMomentEffect E hM A‖ / (n * ε ^ 2) := by
  refine (povm_sample_confidence E hM ρ hρ A hn ε hε).trans ?_
  exact div_le_div_of_nonneg_right (povm_variance_le E hM ρ hρ A)
    (by positivity)

/-- For two observables reconstructed from the same POVM records, the probability that either
sample mean deviates by more than `ε` is bounded by the sum of the moment-effect norms
divided by `n * ε ^ 2`. -/
theorem povm_two_observables_shared_records (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Fin 2 → Operator D) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O => ∃ i : Fin 2,
          ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A i)) ω
            - (Matrix.trace (A i * ρ)).re|)
      ≤ (‖povmMomentEffect E hM (A 0)‖ + ‖povmMomentEffect E hM (A 1)‖)
          / (n * ε ^ 2) := by
  have hub := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound (X := O) (L := n) (M := 2)
    (povmRecordLaw E ρ hρ)
    (fun (i : Fin 2) (ω : Fin n → O) =>
      ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A i)) ω
        - (Matrix.trace (A i * ρ)).re|)
  have h0 := povm_sample_confidence_bound E hM ρ hρ (A 0) hn ε hε
  have h1 := povm_sample_confidence_bound E hM ρ hρ (A 1) hn ε hε
  refine hub.trans ?_
  calc (∑ m : Fin 2, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
          (fun ω : Fin n → O => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (povmStatistic E hM (A m)) ω
            - (Matrix.trace (A m * ρ)).re|))
      ≤ (∑ m : Fin 2, ‖povmMomentEffect E hM (A m)‖ / (n * ε ^ 2)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        fin_cases m
        · exact h0
        · exact h1
    _ = (‖povmMomentEffect E hM (A 0)‖ + ‖povmMomentEffect E hM (A 1)‖)
          / (n * ε ^ 2) := by
        rw [Fin.sum_univ_two]
        ring

/-- Summing the probability weights against the indicator of `x = a` returns the probability of
`a`. -/
theorem prob_ite_sum {O : Type} [Fintype O] [DecidableEq O] (p : FinDist O) (a : O) :
    (∑ x, p.prob x * (if x = a then 1 else 0)) = p.prob a := by
  have hconv : ∀ x, p.prob x * (if x = a then 1 else 0)
      = (if a = x then p.prob x else 0) := by
    intro x
    by_cases h : x = a
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [hconv]
  rw [Fintype.sum_ite_eq]

/-- A finite product equals the product along an injective selection when the selected factors
agree and all unselected factors are one. -/
theorem prod_split_selected {n k : ℕ} (idx : Fin k → Fin n) (hidx : Function.Injective idx) (F : Fin n → ℝ)
    (G : Fin k → ℝ) (hFG : ∀ t, F (idx t) = G t)
    (hfree : ∀ j, (∀ t, idx t ≠ j) → F j = 1) :
    (∏ j : Fin n, F j) = (∏ t : Fin k, G t) := by
  classical
  set S : Finset (Fin n) := Finset.image idx (Finset.univ : Finset (Fin k)) with hS
  have hdisj : Disjoint S ((Finset.univ : Finset (Fin n)) \ S) := by
    refine Finset.disjoint_left.2 ?_
    intro a ha1 ha2
    exact (Finset.mem_sdiff.mp ha2).2 ha1
  have hunion : S ∪ ((Finset.univ : Finset (Fin n)) \ S) = Finset.univ := by
    ext a
    constructor
    · intro _
      exact Finset.mem_univ a
    · intro ha
      by_cases h : a ∈ S
      · exact Finset.mem_union.mpr (Or.inl h)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨ha, h⟩))
  have h1 := Finset.prod_union (f := F) hdisj
  rw [hunion] at h1
  have hinj : Set.InjOn idx ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a ha b hb hab
    exact hidx (by simpa using hab)
  have himage : (∏ j ∈ S, F j) = ∏ t : Fin k, F (idx t) := by
    rw [hS, Finset.prod_image hinj]
  have hrest : (∏ j ∈ (Finset.univ : Finset (Fin n)) \ S, F j) = 1 := by
    refine Finset.prod_eq_one (fun j hj => ?_)
    have hnot : ∀ t, idx t ≠ j := by
      intro t
      intro hcontra
      exact (Finset.mem_sdiff.mp hj).2
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, hcontra⟩)
    exact hfree j hnot
  rw [h1, himage, hrest, mul_one]
  exact Finset.prod_congr rfl fun t _ => hFG t

/-- The joint marginal at injectively selected positions in a product sample law is the product
of the corresponding single-record probabilities. -/
theorem povm_joint_marginal (p : FinDist O) {n k : ℕ} (idx : Fin k → Fin n)
    (hidx : Function.Injective idx) (y : Fin k → O) :
    (∑ ω : Fin n → O, p.probOf ω
        * (∏ t : Fin k, (if ω (idx t) = y t then (1 : ℝ) else 0)))
      = ∏ t : Fin k, p.prob (y t) := by
  classical
  have hsplit : ∀ (ω : Fin n → O),
      (∏ j : Fin n, (∏ t : Fin k,
          (if idx t = j then (if ω j = y t then (1 : ℝ) else 0) else 1)))
        = ∏ t : Fin k, (if ω (idx t) = y t then (1 : ℝ) else 0) := by
    intro ω
    calc (∏ j : Fin n, (∏ t : Fin k,
          (if idx t = j then (if ω j = y t then (1 : ℝ) else 0) else 1)))
        = ∏ t : Fin k, (∏ j : Fin n,
          (if idx t = j then (if ω j = y t then (1 : ℝ) else 0) else 1)) := by
            exact Finset.prod_comm
      _ = ∏ t : Fin k, (if ω (idx t) = y t then (1 : ℝ) else 0) := by
          refine Finset.prod_congr rfl fun t _ => ?_
          have hsingle : (∏ j : Fin n, (if idx t = j then (if ω j = y t then (1 : ℝ) else 0) else 1))
              = (if idx t = idx t then (if ω (idx t) = y t then (1 : ℝ) else 0) else 1) := by
            refine Finset.prod_eq_single (idx t) (fun b hb hne => ?_) (fun h => ?_)
            · rw [if_neg (Ne.symm hne)]
            · exact absurd (Finset.mem_univ (idx t)) h
          rw [hsingle]
          simp
  have hsel : ∀ (t : Fin k) (x : O),
      (∏ t' : Fin k, (if idx t' = idx t then (if x = y t' then (1 : ℝ) else 0) else 1))
        = (if x = y t then (1 : ℝ) else 0) := by
    intro t x
    have hsingle : (∏ t' : Fin k,
        (if idx t' = idx t then (if x = y t' then (1 : ℝ) else 0) else 1))
        = (if idx t = idx t then (if x = y t then (1 : ℝ) else 0) else 1) := by
      refine Finset.prod_eq_single t (fun t' ht' hne => ?_) (fun h => ?_)
      · have : idx t' ≠ idx t := fun h => hne (hidx h)
        simp [this]
      · exact absurd (Finset.mem_univ t) h
    rw [hsingle]
    simp
  have hfree : ∀ (j : Fin n) (x : O), (∀ t, idx t ≠ j) →
      (∏ t : Fin k, (if idx t = j then (if x = y t then (1 : ℝ) else 0) else 1)) = 1 := by
    intro j x hne
    refine Finset.prod_eq_one (fun t _ => ?_)
    have : idx t ≠ j := hne t
    simp [this]
  have hprod : (∏ j : Fin n, (∑ x, p.prob x * (∏ t' : Fin k,
      (if idx t' = j then (if x = y t' then (1 : ℝ) else 0) else 1))))
      = ∏ t : Fin k, p.prob (y t) := by
    refine prod_split_selected idx hidx
      (fun j => ∑ x, p.prob x * (∏ t' : Fin k,
        (if idx t' = j then (if x = y t' then (1 : ℝ) else 0) else 1)))
      (fun t => p.prob (y t)) (fun t => ?_) (fun j hne => ?_)
    · (try dsimp only)
      have hsum : (∑ x, p.prob x * (∏ t' : Fin k,
          (if idx t' = idx t then (if x = y t' then (1 : ℝ) else 0) else 1)))
          = ∑ x, p.prob x * (if x = y t then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact congrArg (fun z => p.prob x * z) (hsel t x)
      rw [hsum]
      exact prob_ite_sum p (y t)
    · (try dsimp only)
      have hsum : (∑ x, p.prob x * (∏ t' : Fin k,
          (if idx t' = j then (if x = y t' then (1 : ℝ) else 0) else 1)))
          = ∑ x, p.prob x * 1 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact congrArg (fun z => p.prob x * z) (hfree j x hne)
      rw [hsum]
      simpa using p.sum_one
  have hp := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod (L := n) p
    (fun j x => ∏ t : Fin k, (if idx t = j then (if x = y t then (1 : ℝ) else 0) else 1))
  simp_rw [hsplit] at hp
  rw [hprod] at hp
  exact hp

/-- A function of injectively selected sample positions has the same expectation as under the
product law on those positions. -/
theorem povm_joint_expect (p : FinDist O) {n k : ℕ} (idx : Fin k → Fin n)
    (hidx : Function.Injective idx) (f : (Fin k → O) → ℝ) :
    (∑ ω : Fin n → O, p.probOf ω * f (fun t => ω (idx t)))
      = ∑ y : Fin k → O, (∏ t : Fin k, p.prob (y t)) * f y := by
  classical
  have hdelta : ∀ (ω : Fin n → O),
      (∑ y : Fin k → O, (∏ t : Fin k, (if ω (idx t) = y t then (1 : ℝ) else 0)) * f y)
        = f (fun t => ω (idx t)) := by
    intro ω
    have hmain : (∑ y : Fin k → O, (∏ t : Fin k,
          (if ω (idx t) = y t then (1 : ℝ) else 0)) * f y)
        = (∏ t : Fin k, (if ω (idx t) = ω (idx t) then (1 : ℝ) else 0))
          * f (fun t => ω (idx t)) := by
      refine Finset.sum_eq_single (fun t => ω (idx t)) (fun y hy hne => ?_)
        (fun hy => ?_)
      · have hex : ∃ t, y t ≠ ω (idx t) := by
          by_contra hcon
          exact hne (funext fun t => by
            by_contra h1
            exact hcon ⟨t, h1⟩)
        obtain ⟨t, ht⟩ := hex
        have hz : (∏ t : Fin k, (if ω (idx t) = y t then (1 : ℝ) else 0)) = 0 := by
          have hz' : (∏ t ∈ (Finset.univ : Finset (Fin k)),
              (if ω (idx t) = y t then (1 : ℝ) else 0)) = 0 := by
            refine Finset.prod_eq_zero (i := t)
              (f := fun t => (if ω (idx t) = y t then (1 : ℝ) else 0))
              (s := (Finset.univ : Finset (Fin k))) (Finset.mem_univ t) ?_
            show (if ω (idx t) = y t then (1 : ℝ) else 0) = 0
            rw [if_neg (Ne.symm ht)]
          exact hz'
        rw [hz, zero_mul]
      · exact absurd (Finset.mem_univ (fun t => ω (idx t))) hy
    rw [hmain]
    simp
  calc (∑ ω : Fin n → O, p.probOf ω * f (fun t => ω (idx t)))
      = ∑ ω : Fin n → O, p.probOf ω
          * (∑ y : Fin k → O, (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0)) * f y) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        exact congrArg (fun z => p.probOf ω * z) (hdelta ω).symm
    _ = ∑ ω : Fin n → O, ∑ y : Fin k → O,
          p.probOf ω * ((∏ t : Fin k, (if ω (idx t) = y t then 1 else 0)) * f y) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ y : Fin k → O, ∑ ω : Fin n → O,
          p.probOf ω * ((∏ t : Fin k, (if ω (idx t) = y t then 1 else 0)) * f y) := by
        exact Finset.sum_comm
    _ = ∑ y : Fin k → O, (∑ ω : Fin n → O, p.probOf ω
          * (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0))) * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        calc (∑ ω : Fin n → O, p.probOf ω
              * ((∏ t : Fin k, (if ω (idx t) = y t then 1 else 0)) * f y))
            = ∑ ω : Fin n → O, f y
              * (p.probOf ω * (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0))) := by
              exact Finset.sum_congr rfl fun ω _ => by ring
          _ = f y * (∑ ω : Fin n → O, p.probOf ω
              * (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0))) := by
            rw [← Finset.mul_sum]
          _ = (∑ ω : Fin n → O, p.probOf ω
              * (∏ t : Fin k, (if ω (idx t) = y t then 1 else 0))) * f y := by ring
    _ = ∑ y : Fin k → O, (∏ t : Fin k, p.prob (y t)) * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [povm_joint_marginal p idx hidx y]

/-- The expectation of a `k`-argument kernel under the product of `k` copies of the finite
distribution `p`. -/
noncomputable def kernelMeanK {k : ℕ} (p : FinDist O) (h : (Fin k → O) → ℝ) : ℝ :=
  ∑ y : Fin k → O, (∏ t : Fin k, p.prob (y t)) * h y

/-- The number of injective maps from `Fin k` to `Fin n`, counting ordered selections of
distinct sample positions. -/
noncomputable def distinctTupleCount (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin n)).filter (fun t => Function.Injective t)).card

/-- The average of a kernel over all ordered injective selections of `k` positions in the sample
record. -/
noncomputable def povmUStatisticK {n k : ℕ} (h : (Fin k → O) → ℝ) (ω : Fin n → O) : ℝ :=
  (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0))
    / ((distinctTupleCount n k : ℕ) : ℝ)

/-- The expectation of the unnormalized sum over injective tuples equals the number of such
tuples times `kernelMeanK`. -/
theorem povmUStatisticK_unbiased_scaled (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ) :
    (∑ ω : Fin n → O, p.probOf ω
        * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0)))
      = ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h := by
  classical
  have hswap : (∑ ω : Fin n → O, p.probOf ω
        * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0)))
      = ∑ t : Fin k → Fin n, (if Function.Injective t then
          (∑ ω : Fin n → O, p.probOf ω * h (fun s => ω (t s))) else 0) := by
    calc (∑ ω : Fin n → O, p.probOf ω
          * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0)))
        = ∑ ω : Fin n → O, ∑ t : Fin k → Fin n,
            p.probOf ω * (if Function.Injective t then h (fun s => ω (t s)) else 0) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum]
        _ = ∑ t : Fin k → Fin n, ∑ ω : Fin n → O,
            p.probOf ω * (if Function.Injective t then h (fun s => ω (t s)) else 0) := by
          exact Finset.sum_comm
        _ = ∑ t : Fin k → Fin n, (if Function.Injective t then
            (∑ ω : Fin n → O, p.probOf ω * h (fun s => ω (t s))) else 0) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases ht : Function.Injective t
          · simp only [ht, if_pos]
          · simp [ht]
  have hjoint : ∀ t : Fin k → Fin n, Function.Injective t →
      (∑ ω : Fin n → O, p.probOf ω * h (fun s => ω (t s))) = kernelMeanK p h := by
    intro t ht
    have := povm_joint_expect p t ht h
    simpa [kernelMeanK] using this
  have hcount' : (∑ t : Fin k → Fin n, (if Function.Injective t then kernelMeanK p h else 0))
      = ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h := by
    calc (∑ t : Fin k → Fin n, (if Function.Injective t then kernelMeanK p h else 0))
        = ∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)),
            (if Function.Injective t then kernelMeanK p h else 0) := rfl
      _ = ∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
            (fun t => Function.Injective t), kernelMeanK p h := by
        rw [Finset.sum_filter]
      _ = ((Finset.univ : Finset (Fin k → Fin n)).filter
            (fun t => Function.Injective t)).card * kernelMeanK p h := by
        have h := Finset.sum_const (s := (Finset.univ : Finset (Fin k → Fin n)).filter
            (fun t => Function.Injective t)) (b := kernelMeanK p h)
        rw [nsmul_eq_mul] at h
        exact h
      _ = ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h := by
        simp [distinctTupleCount]
  calc (∑ ω : Fin n → O, p.probOf ω
        * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0)))
      = ∑ t : Fin k → Fin n, (if Function.Injective t then
          (∑ ω : Fin n → O, p.probOf ω * h (fun s => ω (t s))) else 0) := hswap
    _ = ∑ t : Fin k → Fin n, (if Function.Injective t then kernelMeanK p h else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : Function.Injective t
        · simp only [ht, if_pos]
          exact hjoint t ht
        · simp [ht]
    _ = ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h := hcount'

/-- The kernel average over injective tuples has expectation `kernelMeanK` when at least one
injective tuple exists. -/
theorem povmUStatisticK_unbiased (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (hcount : (distinctTupleCount n k : ℕ) ≠ 0) :
    (∑ ω : Fin n → O, p.probOf ω * povmUStatisticK h ω) = kernelMeanK p h := by
  classical
  set C : ℝ := ((distinctTupleCount n k : ℕ) : ℝ) with hC
  have hCne : C ≠ 0 := by
    simp only [hC]
    exact_mod_cast hcount
  calc (∑ ω : Fin n → O, p.probOf ω * povmUStatisticK h ω)
      = ∑ ω : Fin n → O, (p.probOf ω
          * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0))) / C := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [povmUStatisticK, hC]
        field_simp [hCne]
    _ = (∑ ω : Fin n → O, p.probOf ω
          * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0))) / C := by
        have h := Finset.sum_div (s := (Finset.univ : Finset (Fin n → O)))
          (f := fun ω => p.probOf ω
            * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun s => ω (t s)) else 0)))
          (a := C)
        exact h.symm
    _ = (C * kernelMeanK p h) / C := by
        rw [povmUStatisticK_unbiased_scaled p h]
    _ = kernelMeanK p h := by field_simp [hCne]

/-- Counted insertion produces a permutation of the inserted element followed by the original
rational list. -/
theorem rationalInsertSortedCounted_perm (x : ℚ) (l : List ℚ) :
    (rationalInsertSortedCounted x l).1.Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [rationalInsertSortedCounted]
      split
      · exact List.Perm.refl _
      · exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

/-- Counted insertion preserves nondecreasing order of a rational list. -/
theorem rationalInsertSortedCounted_sorted {x : ℚ} {l : List ℚ} (hl : l.SortedLE) :
    (rationalInsertSortedCounted x l).1.SortedLE := by
  induction l with
  | nil =>
      exact List.sortedLE_iff_pairwise.mpr
        (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil (a := b)))
          List.Pairwise.nil)
  | cons y ys ih =>
      simp only [rationalInsertSortedCounted]
      rw [List.sortedLE_iff_pairwise] at hl ⊢
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      split
      · next hxy =>
          refine List.Pairwise.cons (fun b hb => ?_) hl
          rcases List.mem_cons.mp hb with rfl | hbys
          · exact hxy
          · exact le_trans hxy (hhead b hbys)
      · next hnxy =>
          have hyx : y ≤ x := le_of_lt (lt_of_not_ge hnxy)
          refine List.Pairwise.cons (fun b hb => ?_)
            (List.sortedLE_iff_pairwise.mp (ih (List.sortedLE_iff_pairwise.mpr htail)))
          have hmem : b ∈ x :: ys :=
            List.Perm.subset (rationalInsertSortedCounted_perm x ys) hb
          rcases List.mem_cons.mp hmem with rfl | hbys
          · exact hyx
          · exact hhead b hbys

/-- Counted insertion sort returns a permutation of its rational input list. -/
theorem rationalInsertionSortCounted_perm (l : List ℚ) :
    (rationalInsertionSortCounted l).1.Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      show ((rationalInsertSortedCounted x (rationalInsertionSortCounted xs).1).1).Perm (x :: xs)
      exact List.Perm.trans (rationalInsertSortedCounted_perm x _) (List.Perm.cons x ih)

/-- Counted insertion sort returns a nondecreasing rational list. -/
theorem rationalInsertionSortCounted_sorted (l : List ℚ) :
    (rationalInsertionSortCounted l).1.SortedLE := by
  induction l with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons x xs ih =>
      show ((rationalInsertSortedCounted x (rationalInsertionSortCounted xs).1).1).SortedLE
      exact rationalInsertSortedCounted_sorted ih

/-- For a nonempty list of length `K`, the sorted entry at index `K / 2` lies above all earlier
entries and below all later valid entries. -/
theorem rationalInsertionSortCounted_median_property {K : ℕ} (means : List ℚ)
    (hK : 0 < K) (hlen : means.length = K) :
    (∀ j, j < K / 2 →
        (rationalInsertionSortCounted means).1.getD j 0
          ≤ (rationalInsertionSortCounted means).1.getD (K / 2) 0)
      ∧ (∀ j, K / 2 < j → j < means.length →
        (rationalInsertionSortCounted means).1.getD (K / 2) 0
          ≤ (rationalInsertionSortCounted means).1.getD j 0) := by
  classical
  set s : List ℚ := (rationalInsertionSortCounted means).1 with hs
  have hlen' : s.length = K := by
    rw [hs, rationalInsertionSortCounted_length]
    exact hlen
  have hsorted : s.SortedLE := by
    rw [hs]
    exact rationalInsertionSortCounted_sorted means
  have hmid : K / 2 < s.length := by
    have hk : K / 2 < K := by omega
    omega
  have hpw : ∀ (i j : ℕ) (_hi : i < s.length) (_hj : j < s.length), i < j → s[i] ≤ s[j] := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp (List.sortedLE_iff_pairwise.mp hsorted)) i j hi hj hij
  refine ⟨?_, ?_⟩
  · intro j hj
    have hjlt : j < s.length := by
      have : j < K / 2 := by omega
      omega
    have hgetj : s.getD j 0 = s[j] := List.getD_eq_getElem s 0 hjlt
    have hgetm : s.getD (K / 2) 0 = s[K / 2] := List.getD_eq_getElem s 0 hmid
    rw [hgetj, hgetm]
    exact hpw j (K / 2) hjlt hmid (by omega)
  · intro j hj hjs
    have hjlt : j < s.length := by
      rw [hlen', ← hlen]
      exact hjs
    have hgetj : s.getD j 0 = s[j] := List.getD_eq_getElem s 0 hjlt
    have hgetm : s.getD (K / 2) 0 = s[K / 2] := List.getD_eq_getElem s 0 hmid
    rw [hgetj, hgetm]
    exact hpw (K / 2) j hmid hjlt hj

/-- The axis-table entry indexed by the sum of recorded outcome labels modulo three. -/
def nativeResultDependentAxis (history : List (Fin 3 × Fin 2)) : Fin 3 :=
  nativeAxisTable.getD (history.foldl (fun acc r => (acc + r.2.val) % 3) 0) 0

/-- Changing the indicated outcome label changes the axis selected for the two displayed
histories. -/
theorem nativeResultDependentAxis_depends_on_labels :
    nativeResultDependentAxis [(0, 0), (0, 0)] ≠ nativeResultDependentAxis [(0, 1), (0, 0)] := by
  simp [nativeResultDependentAxis, nativeAxisTable]

/-- On the displayed history, outcome-dependent axis selection differs from `nativeSelectAxis`. -/
theorem nativeResultDependentAxis_ne_length_based :
    nativeResultDependentAxis [(0, 1), (0, 0)] ≠ nativeSelectAxis [(0, 1), (0, 0)] := by
  simp [nativeResultDependentAxis, nativeSelectAxis, nativeAxisTable]

/-- The history length plus the draw cost of the axis selected from its outcome labels. -/
def nativeResultDependentAxisCost (history : List (Fin 3 × Fin 2)) : ℕ :=
  history.length + nativeAxisDrawCost (nativeResultDependentAxis history)

/-- Outcome-dependent axis selection costs at most the history length plus the axis-table
length. -/
theorem nativeResultDependentAxisCost_le (history : List (Fin 3 × Fin 2)) :
    nativeResultDependentAxisCost history ≤ history.length + nativeAxisTable.length := by
  exact Nat.add_le_add (Nat.le_refl _) (nativeAxisDrawCost_le _)

/-- Appending one record updates the axis-table index by adding its outcome label modulo three. -/
theorem nativeResultDependentAxis_append (history : List (Fin 3 × Fin 2))
    (r : Fin 3 × Fin 2) :
    nativeResultDependentAxis (history ++ [r])
      = nativeAxisTable.getD
          ((history.foldl (fun acc x => (acc + x.2.val) % 3) 0 + r.2.val) % 3) 0 := by
  simp [nativeResultDependentAxis, List.foldl_append]

end MeasuredStatistics
end Qatlib.Concepts.MbqcFlow.FlowDecision
