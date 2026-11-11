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
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout

/-!
# Population tail moments and empirical confidence bounds

This module defines population and empirical truncated loss moments and their ratios to
cumulative probability. The ratios `populationCVaR` and `empiricalCVaR` use the threshold
restricted payoff, with the lower tail convention used by this development of quantum risk
analysis [WoernerEgger2019].

Finite sample variance and union bounds control CDF and tail moment errors over a threshold
list. A separate ratio stability theorem transfers simultaneous numerator and denominator
accuracy to conditional mean accuracy when the population denominator is sufficiently large.

## Main statements

* `bounded_variance_le_quarter`: variance bound for a payoff in the unit interval.
* `population_cvar_ratio_stability`: conditional mean error under denominator separation.
* `population_cvar_confidence_mass`: the finite threshold table failure bound.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

/-- The independent product PMF obtained by sampling once from each of the two supplied PMFs. -/
noncomputable def populationJointLaw {α β : Type} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  PMF.bind p (fun a => PMF.map (fun b => (a, b)) q)

/-- The shared rational label readout `labelReadout` at size `M` and precision `b`. -/
noncomputable def s3Readout (M : ℕ) (b : ℕ) (z : Fin M) : ℚ :=
  labelReadout M b z

/-- The nearest integer count readout `countLabelReadoutNearest` at population size `N`. -/
noncomputable def s3Count (N : ℕ) (M : ℕ) (z : Fin M) : ℕ :=
  countLabelReadoutNearest N M z

/-- A real payoff taking values in `[0, 1]` under a finite probability distribution has variance
at most one quarter. -/
theorem bounded_variance_le_quarter {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    p.variance f ≤ 1/4 := by
  set μ := p.expect f with hμ
  have hsq : ∀ x, (f x)^2 ≤ f x := by
    intro x
    calc (f x)^2 = f x * f x := by ring
      _ ≤ f x * 1 := mul_le_mul_of_nonneg_left (hf x).2 (hf x).1
      _ = f x := by ring
  have hsum_add : ∀ (u v : X → ℝ),
      p.expect (fun x => u x + v x) = p.expect u + p.expect v := by
    intro u v
    calc
      p.expect (fun x => u x + v x)
          = Finset.univ.sum (fun x => ((p.prob x * u x) + (p.prob x * v x))) := by
            unfold FinDist.expect
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = Finset.univ.sum (fun x => p.prob x * u x)
          + Finset.univ.sum (fun x => p.prob x * v x) := by
            exact Finset.sum_add_distrib (s := Finset.univ)
              (f := fun x => p.prob x * u x) (g := fun x => p.prob x * v x)
      _ = p.expect u + p.expect v := by
        unfold FinDist.expect
        rfl
  have hpoint : ∀ x, (f x - μ)^2 ≤ f x - 2*μ*f x + μ^2 := by
    intro x
    calc (f x - μ)^2 = (f x)^2 - 2*μ*f x + μ^2 := by ring
      _ ≤ f x - 2*μ*f x + μ^2 := by linarith [hsq x]
  have hE : p.expect (fun x => (f x - μ)^2)
      ≤ p.expect (fun x => f x - 2*μ*f x + μ^2) := by
    unfold FinDist.expect
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (p.nonneg x)
  have hEh : p.expect (fun x => f x - 2*μ*f x + μ^2)
      = p.expect (fun x => (1-2*μ) * f x) + μ^2 := by
    calc
      p.expect (fun x => f x - 2*μ*f x + μ^2)
          = p.expect (fun x => ((f x - 2*μ*f x) + μ^2)) := by congr 1
      _ = p.expect (fun x => f x - 2*μ*f x) + p.expect (fun _ => μ^2) := hsum_add _ _
      _ = p.expect (fun x => (1-2*μ) * f x) + μ^2 := by
        have he : (fun x : X => f x - 2*μ*f x) = (fun x : X => (1-2*μ) * f x) := by
          funext x
          ring
        rw [he, ProbabilityInterfaces.expect_const_mul, FinDist.expect_const]
  have hvar : p.variance f = p.expect (fun x => (f x - μ)^2) := by
    unfold FinDist.variance
    rw [← hμ]
  rw [hvar]
  have h1 : p.expect (fun x => (f x - μ)^2) ≤ μ - μ^2 := by
    calc
      p.expect (fun x => (f x - μ)^2)
          ≤ p.expect (fun x => f x - 2*μ*f x + μ^2) := hE
      _ = p.expect (fun x => (1-2*μ) * f x) + μ^2 := hEh
      _ = (1-2*μ) * p.expect f + μ^2 := by rw [ProbabilityInterfaces.expect_const_mul]
      _ = (1-2*μ) * μ + μ^2 := by rw [← hμ]
      _ = μ - μ^2 := by ring
  have h2 : μ - μ^2 ≤ 1/4 := by nlinarith [sq_nonneg (2*μ - 1)]
  linarith

/-- The event mass under the independent sample law equals `FinDist.probEvent` for the same
repeated finite distribution. -/
theorem iid_mass_eq_probEvent (p : FinDist (Option (Fin n)))
    (E : (Fin N → Option (Fin n)) → Prop) :
    Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p)) E
      = FinDist.probEvent (L := N) p E := by
  classical
  unfold Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass FinDist.probEvent
  apply Finset.sum_congr rfl
  intro ω _
  rfl

/-- The probability of a union of two sample events is at most the sum of their probabilities. -/
theorem probEvent_or_le {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) {L : ℕ}
    (A B : (Fin L → X) → Prop) :
    FinDist.probEvent (L := L) p (fun ω => A ω ∨ B ω)
      ≤ FinDist.probEvent (L := L) p A + FinDist.probEvent (L := L) p B := by
  classical
  have hq : ∀ ω : Fin L → X, 0 ≤ p.probOf ω := by
    intro ω
    exact Finset.prod_nonneg fun i _ => p.nonneg (ω i)
  have hstep : ∀ ω : Fin L → X, A ω ∨ B ω →
      p.probOf ω ≤ (if A ω then p.probOf ω else 0) + (if B ω then p.probOf ω else 0) := by
    intro ω h
    have h0 := hq ω
    by_cases hA : A ω
    · by_cases hB : B ω
      · rw [if_pos hA, if_pos hB]
        linarith
      · rw [if_pos hA, if_neg hB]
        linarith
    · have hB : B ω := h.resolve_left hA
      rw [if_neg hA, if_pos hB]
      linarith
  have hAeq : Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
        (fun ω => if A ω then p.probOf ω else 0)
      = Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω))
        (fun ω => p.probOf ω) := by
    have hsub : Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω))
        (fun ω => if A ω then p.probOf ω else 0)
        = Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
          (fun ω => if A ω then p.probOf ω else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro ω hω
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hω).2⟩
      · intro ω hω hnot
        by_cases hA : A ω
        · exfalso
          have hm : ω ∈ Finset.filter (fun ω => A ω)
              (Finset.univ : Finset (Fin L → X)) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hA⟩
          exact hnot hm
        · rw [if_neg hA]
    rw [← hsub]
    exact Finset.sum_congr rfl (fun ω hω => by rw [if_pos (Finset.mem_filter.mp hω).2])
  have hBeq : Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
        (fun ω => if B ω then p.probOf ω else 0)
      = Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => B ω))
        (fun ω => p.probOf ω) := by
    have hsub : Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => B ω))
        (fun ω => if B ω then p.probOf ω else 0)
        = Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
          (fun ω => if B ω then p.probOf ω else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro ω hω
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hω).2⟩
      · intro ω hω hnot
        by_cases hB : B ω
        · exfalso
          have hm : ω ∈ Finset.filter (fun ω => B ω)
              (Finset.univ : Finset (Fin L → X)) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hB⟩
          exact hnot hm
        · rw [if_neg hB]
    rw [← hsub]
    exact Finset.sum_congr rfl (fun ω hω => by rw [if_pos (Finset.mem_filter.mp hω).2])
  unfold FinDist.probEvent
  calc
    Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
        (fun ω => p.probOf ω)
      ≤ Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
        (fun ω => (if A ω then p.probOf ω else 0) + (if B ω then p.probOf ω else 0)) := by
        exact Finset.sum_le_sum fun ω hω => hstep ω (Finset.mem_filter.mp hω).2
    _ = (Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
          (fun ω => if A ω then p.probOf ω else 0))
        + (Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω ∨ B ω))
          (fun ω => if B ω then p.probOf ω else 0)) := by
        exact (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin L → X)).filter
          (fun ω => A ω ∨ B ω))
          (f := fun ω => if A ω then p.probOf ω else 0)
          (g := fun ω => if B ω then p.probOf ω else 0))
    _ = (Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => A ω))
          (fun ω => p.probOf ω))
        + (Finset.sum ((Finset.univ : Finset (Fin L → X)).filter (fun ω => B ω))
          (fun ω => p.probOf ω)) := by rw [hAeq, hBeq]

/-- The expectation of the rational threshold restricted tail payoff under the population
distribution. -/
noncomputable def populationTailMoment {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) : ℝ :=
  ∑ a, p.prob a * (riskTailPayoff loss t a : ℝ)

/-- The population threshold restricted tail moment divided by the population CDF at that
threshold. -/
noncomputable def populationCVaR {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) : ℝ :=
  populationTailMoment p loss t / populationCDF p loss t

/-- The sample average of the threshold restricted rational tail payoff, computed using
empirical multiplicities. -/
noncomputable def empiricalTailMoment {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) : ℝ :=
  (((∑ a, empiricalWeight ω a * riskTailPayoff loss t a) / (N : ℚ) : ℚ) : ℝ)

/-- The empirical threshold restricted tail moment divided by the empirical CDF. -/
noncomputable def empiricalCVaR {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) : ℝ :=
  empiricalTailMoment ω loss t / (empiricalCDF ω loss t : ℝ)

/-- The population tail moment equals the finite distribution expectation of the threshold
restricted payoff. -/
theorem population_tail_moment_eq_expect {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) :
    populationTailMoment p loss t = p.expect (fun i => (riskTailPayoff loss t i : ℝ)) := by
  rfl

/-- The empirical tail moment equals the sample average of the threshold restricted payoff. -/
theorem empirical_tail_moment_eq_avg (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) :
    empiricalTailMoment ω loss t = FinDist.avg (fun i => (riskTailPayoff loss t i : ℝ)) ω := by
  classical
  have hf : ∑ a, (empiricalWeight ω a : ℚ) * riskTailPayoff loss t a
      = ∑ k, (riskTailPayoff loss t (ω k) : ℚ) := by
    have h := empirical_count_sum (List.ofFn ω) (fun a => riskTailPayoff loss t a)
    simp only [empiricalWeight]
    rw [h, List.map_ofFn, List.sum_ofFn]
    rfl
  unfold empiricalTailMoment
  rw [hf]
  push_cast
  unfold FinDist.avg
  rfl

/-- For losses in `[0, 1]` and positive sample size and tolerance, empirical tail moment error
exceeds `ν` with mass at most `1 / (4 * N * ν ^ 2)`. -/
theorem empirical_tail_moment_sampling_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν)
    (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) :
    Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p))
      (fun ω : Fin N → Option (Fin n) =>
        ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|)
      ≤ 1/(4*(N : ℝ)*ν^2) := by
  classical
  rw [iid_mass_eq_probEvent]
  have hcheb := p.chebyshev_avg (fun i => (riskTailPayoff loss t i : ℝ)) hN ν hν
  simp only [← empirical_tail_moment_eq_avg, ← population_tail_moment_eq_expect] at hcheb
  apply hcheb.trans
  have hvar : p.variance (fun i => (riskTailPayoff loss t i : ℝ)) ≤ 1/4 := by
    apply bounded_variance_le_quarter
    intro i
    have h := riskTailPayoff_bounds loss t hloss i
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hd : 0 < (N : ℝ)*ν^2 := mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hν)
  calc
    _ ≤ (1/4 : ℝ)/((N : ℝ)*ν^2) := div_le_div_of_nonneg_right hvar hd.le
    _ = _ := by ring

/-- For bounded losses, simultaneous CDF and tail moment errors at most `η` yield conditional
mean error at most `4 * η / populationCDF p loss t` when `2 * η` is below the positive
population CDF. -/
theorem population_cvar_ratio_stability {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (η : ℝ) (ω : Fin N → Option (Fin n))
    (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) (hη : 0 ≤ η)
    (hc : |(empiricalCDF ω loss t : ℝ) - populationCDF p loss t| ≤ η)
    (hm : |empiricalTailMoment ω loss t - populationTailMoment p loss t| ≤ η)
    (hp : 0 < populationCDF p loss t) (hgap : 2*η < populationCDF p loss t) :
    |empiricalCVaR ω loss t - populationCVaR p loss t| ≤ 4*η/populationCDF p loss t := by
  have ha0 : 0 ≤ empiricalTailMoment ω loss t := by
    rw [empirical_tail_moment_eq_avg]
    unfold FinDist.avg
    have hsum : 0 ≤ ∑ k, (riskTailPayoff loss t (ω k) : ℝ) := by
      apply Finset.sum_nonneg
      intro k _
      have h := riskTailPayoff_bounds loss t hloss (ω k)
      exact_mod_cast h.1
    positivity
  have haφ : empiricalTailMoment ω loss t ≤ (empiricalCDF ω loss t : ℝ) := by
    rw [empirical_tail_moment_eq_avg, empiricalCDF_avg]
    unfold FinDist.avg
    have hpt : ∀ k : Fin N, (riskTailPayoff loss t (ω k) : ℝ)
        ≤ riskCDFPayoff loss t (ω k) := by
      intro k
      have h := riskTailPayoff_bounds loss t hloss (ω k)
      have hle : (loss (ω k) : ℝ) ≤ 1 := by exact_mod_cast (hloss (ω k)).2
      by_cases ht : loss (ω k) ≤ t
      · simp only [riskTailPayoff, riskCDFPayoff, if_pos ht]
        exact hle
      · simp only [riskTailPayoff, riskCDFPayoff, if_neg ht]
        norm_num
    have hsum : (∑ k, (riskTailPayoff loss t (ω k) : ℝ))
        ≤ ∑ k, riskCDFPayoff loss t (ω k) := Finset.sum_le_sum fun k _ => hpt k
    exact div_le_div_of_nonneg_right hsum (by positivity)
  have h := empirical_ratio_error (populationCDF p loss t) (populationTailMoment p loss t)
    (empiricalCDF ω loss t : ℝ) (empiricalTailMoment ω loss t) η hη hp hgap hc hm ha0 haφ
  exact h

/-- The sample event that some listed threshold has CDF or tail moment error exceeding `ν`. -/
def badTable {n N : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
    (xs : List ℚ) (ν : ℝ) : (Fin N → Option (Fin n)) → Prop := fun ω =>
  (∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
  ∨ (∃ t ∈ xs, ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|)

/-- For losses in `[0, 1]`, the probability of tail moment error above `ν` at any listed
threshold is at most `xs.length / (4 * N * ν ^ 2)`. -/
theorem empirical_uniform_tail_moment_sampling_bound {n N : ℕ}
    (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ) (xs : List ℚ)
    (ν : ℝ) (hN : 0 < N) (hν : 0 < ν) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|)
      ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin xs.length → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    ν < |empiricalTailMoment ω loss (xs.get i) - populationTailMoment p loss (xs.get i)|
  have he ω : ((∃ t ∈ xs, ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|))
      ↔ ∃ i : Fin xs.length, E i ω := by
    constructor
    · rintro ⟨t, ht, hv⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
      exact ⟨i, hv⟩
    · rintro ⟨i, hi⟩
      exact ⟨xs.get i, List.get_mem _ _, hi⟩
  have h := p.union_bound (L := N) (M := xs.length) E
  have hs : FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|)
      = FinDist.probEvent (L := N) p (fun ω => ∃ i, E i ω) := by
    unfold FinDist.probEvent
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin xs.length, FinDist.probEvent (L := N) p (E i))
      ≤ ∑ i : Fin xs.length, 1/(4*(N : ℝ)*ν^2) :=
      Finset.sum_le_sum (fun i _ => empirical_tail_moment_sampling_bound p loss (xs.get i)
        ν hN hν hloss)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The probability of CDF error above `ν` at any listed threshold is at most `xs.length / (4 *
N * ν ^ 2)` for positive sample size and tolerance. -/
theorem empirical_uniform_cdf_sampling_bound {n N : ℕ}
    (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ) (xs : List ℚ)
    (ν : ℝ) (hN : 0 < N) (hν : 0 < ν) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
      ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin xs.length → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    ν < |(empiricalCDF ω loss (xs.get i) : ℝ)-populationCDF p loss (xs.get i)|
  have he ω : ((∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|))
      ↔ ∃ i : Fin xs.length, E i ω := by
    constructor
    · rintro ⟨t, ht, hv⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
      exact ⟨i, hv⟩
    · rintro ⟨i, hi⟩
      exact ⟨xs.get i, List.get_mem _ _, hi⟩
  have h := p.union_bound (L := N) (M := xs.length) E
  have hs : FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
      = FinDist.probEvent (L := N) p (fun ω => ∃ i, E i ω) := by
    unfold FinDist.probEvent
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin xs.length, FinDist.probEvent (L := N) p (E i))
      ≤ ∑ i : Fin xs.length, 1/(4*(N : ℝ)*ν^2) :=
      Finset.sum_le_sum (fun i _ => empirical_cdf_sampling_bound p loss (xs.get i) ν hN hν)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For bounded losses, the probability of either CDF or tail moment error exceeding `ν` at one
threshold is bounded by the sum of their two sampling bounds. -/
theorem empirical_threshold_bad_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν)
    (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        (ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
        ∨ (ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|))
      ≤ 1/(4*(N : ℝ)*ν^2) + 1/(4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin 2 → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    if i = 0 then ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|
    else ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|
  have he ω : ((ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
      ∨ (ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|))
      ↔ ∃ i : Fin 2, E i ω := by
    constructor
    · intro h
      rcases h with h | h
      · refine ⟨0, ?_⟩
        simp only [E, if_pos rfl]
        exact h
      · refine ⟨1, ?_⟩
        simp only [E, if_neg (by decide : ¬((1 : Fin 2) = 0))]
        exact h
    · rintro ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0
        simp only [E, if_pos rfl] at hi
        exact Or.inl hi
      · have h1 : i = 1 := by omega
        subst h1
        simp only [E, if_neg (by decide : ¬((1 : Fin 2) = 0))] at hi
        exact Or.inr hi
  have h := p.union_bound (L := N) (M := 2) E
  have hs : FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        (ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|)
        ∨ (ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|))
      = FinDist.probEvent (L := N) p (fun ω => ∃ i, E i ω) := by
    unfold FinDist.probEvent
    congr 1
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin 2, FinDist.probEvent (L := N) p (E i))
      = FinDist.probEvent (L := N) p (E 0) + FinDist.probEvent (L := N) p (E 1) := by
        rw [Fin.sum_univ_two]
    _ ≤ 1/(4*(N : ℝ)*ν^2) + 1/(4*(N : ℝ)*ν^2) := by
      simp only [E]
      exact add_le_add (empirical_cdf_sampling_bound p loss t ν hN hν)
        (empirical_tail_moment_sampling_bound p loss t ν hN hν hloss)

/-- For bounded losses, the probability of `badTable` is at most twice `xs.length / (4 * N * ν ^
2)`. -/
theorem population_cvar_confidence_mass {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν)
    (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) :
    FinDist.probEvent (L := N) p (badTable p loss xs ν)
      ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) + (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin xs.length → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    (ν < |(empiricalCDF ω loss (xs.get i) : ℝ)-populationCDF p loss (xs.get i)|)
    ∨ (ν < |empiricalTailMoment ω loss (xs.get i) - populationTailMoment p loss (xs.get i)|)
  have he ω : badTable p loss xs ν ω ↔ ∃ i : Fin xs.length, E i ω := by
    constructor
    · intro h
      rcases h with ⟨t, ht, hv⟩ | ⟨t, ht, hv⟩
      · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
        refine ⟨i, Or.inl hv⟩
      · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
        refine ⟨i, Or.inr hv⟩
    · rintro ⟨i, hi⟩
      rcases hi with hi | hi
      · exact Or.inl ⟨xs.get i, List.get_mem _ _, hi⟩
      · exact Or.inr ⟨xs.get i, List.get_mem _ _, hi⟩
  have h := p.union_bound (L := N) (M := xs.length) E
  have hs : FinDist.probEvent (L := N) p (badTable p loss xs ν)
      = FinDist.probEvent (L := N) p (fun ω => ∃ i, E i ω) := by
    unfold FinDist.probEvent
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin xs.length, FinDist.probEvent (L := N) p (E i))
      ≤ ∑ i : Fin xs.length, (1/(4*(N : ℝ)*ν^2) + 1/(4*(N : ℝ)*ν^2)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        simp only [E]
        exact empirical_threshold_bad_bound p loss (xs.get i) ν hN hν hloss
    _ = (xs.length : ℝ)/(4*(N : ℝ)*ν^2) + (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The independent sample law mass of `badTable` is at most twice `xs.length / (4 * N * ν ^ 2)`
under the bounded loss and positivity hypotheses. -/
theorem population_cvar_bad_mass {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν)
    (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) :
    Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p)) (badTable p loss xs ν)
      ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) + (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  classical
  have heq : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p))
        (badTable p loss xs ν)
      = FinDist.probEvent (L := N) p (badTable p loss xs ν) :=
    iid_mass_eq_probEvent p (badTable p loss xs ν)
  rw [heq]
  exact population_cvar_confidence_mass p loss xs ν hN hν hloss
end Qatlib.Concepts.RiskEstimation.PopulationGap
