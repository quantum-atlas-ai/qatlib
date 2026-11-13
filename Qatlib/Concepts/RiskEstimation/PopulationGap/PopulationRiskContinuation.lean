/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.PopulationRiskContinuationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ContinuousMarketCDFDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ExactVaRProgramDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitAccessDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitLedgerDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketProgramResourcesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketQuantizationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketQuantumReadDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.PopulationRiskCVaRDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.RiskEmitterDefs

/-!
# Population risk guarantees and implementation interfaces

This module assembles population CDF and conditional mean guarantees, quantile separation
results, and finite grid approximation interfaces for quantum risk readout [WoernerEgger2019].
`clause22_endpoint` combines sampling and numerical preparation error with quantum readout
error, while `clause23_endpoint` records quantile guarantees and a finite sample
indistinguishability obstruction.

The remaining interfaces collect signed dyadic loading, phase approximation, emitter decisions,
grid window error, and explicit program resource accounting.

## Main statements

* `clause22_endpoint`: population conditional mean confidence and readout guarantees.
* `clause23_endpoint`: quantile index properties and sampling limitations.
* `clause24_endpoint`: signed loading and phase emitter guarantees.
* `clause25_endpoint`: loaded grid CDF error and resource bounds.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators Matrix.Norms.L2Operator
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

/-- For a PMF on pairs, the event that either coordinate satisfies its predicate has mass at
most the sum of the coordinate event masses. -/
theorem population_joint_union_le {α β : Type} (p : PMF (α × β))
    (E1 : α → Prop) (E2 : β → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => E1 x.1 ∨ E2 x.2)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => E1 x.1) + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => E2 x.2) := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  refine le_trans (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
    (f := fun (x : α × β) => @ite ℝ≥0∞ (E1 x.1 ∨ E2 x.2)
        (Classical.propDecidable (E1 x.1 ∨ E2 x.2)) 1 0)
    (g := fun (x : α × β) => @ite ℝ≥0∞ (E1 x.1) (Classical.propDecidable (E1 x.1)) 1 0
                  + @ite ℝ≥0∞ (E2 x.2) (Classical.propDecidable (E2 x.2)) 1 0) ?_) ?_
  · intro x
    by_cases h1 : E1 x.1 <;> by_cases h2 : E2 x.2 <;> simp [h1, h2]
  · rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]

/-- The section readout `s3Readout` equals the shared rational label readout. -/
theorem s3_readout_is_shared_engine_readout (M : ℕ) (b : ℕ) (z : Fin M) :
    s3Readout M b z = labelReadout M b z := rfl

/-- The section count `s3Count` equals the shared nearest integer count readout. -/
theorem s3_count_is_shared_engine_count (N : ℕ) (M : ℕ) (z : Fin M) :
    s3Count N M z = countLabelReadoutNearest N M z := rfl

/-- The section count differs from the scaled amplitude estimate `N * aeEstimate M z` by at most
one half. -/
theorem s3_per_occasion_quantum_error_le (N : ℕ) (M : ℕ) (z : Fin M) :
    |(s3Count N M z : ℝ) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 :=
  countLabelReadoutNearest_error N M z

/-- The section count never exceeds the population size `N`. -/
theorem s3_per_occasion_count_valid (N : ℕ) (M : ℕ) (z : Fin M) :
    s3Count N M z ≤ N :=
  countLabelReadoutNearest_le N M z

/-- Combines population conditional mean identities, tail moment sampling bounds, ratio
stability, and an end to end quantum conditional mean failure bound under the stated
separation and precision hypotheses. -/
theorem clause22_endpoint :
    ∀ (n N : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
      (xs : List ℚ) (t : ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν)
      (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1),

      (populationCVaR p loss t = populationTailMoment p loss t / populationCDF p loss t) ∧

      (Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p))
        (fun ω : Fin N → Option (Fin n) =>
          ν < |empiricalTailMoment ω loss t - populationTailMoment p loss t|)
        ≤ 1/(4*(N : ℝ)*ν^2)) ∧

      (FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
          ∃ t' ∈ xs, ν < |empiricalTailMoment ω loss t' - populationTailMoment p loss t'|)
        ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2)) ∧

      (∀ (η : ℝ) (ω : Fin N → Option (Fin n)) (hη : 0 ≤ η)
        (hc : |(empiricalCDF ω loss t : ℝ) - populationCDF p loss t| ≤ η)
        (hm : |empiricalTailMoment ω loss t - populationTailMoment p loss t| ≤ η)
        (hp : 0 < populationCDF p loss t) (hgap : 2*η < populationCDF p loss t),
        |empiricalCVaR ω loss t - populationCVaR p loss t| ≤ 4*η/populationCDF p loss t) ∧

      (FinDist.probEvent (L := N) p (badTable p loss xs ν)
        ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) + (xs.length : ℝ)/(4*(N : ℝ)*ν^2)) ∧

      (∀ (bits payoffBits M r v : ℕ) (q eps : ℝ)
        (hM : 2 ≤ M) (hxs : xs ≠ []) (hsorted : xs.SortedLE)
        (hsupport : ∀ a, loss a ∈ xs) (hq0 : 0 < q) (hq1 : q < 1) (heps : 0 < eps)
        (hv : v < xs.length) (ht : xs.getD v 0 = t)
        (hwindow : Real.pi/M+Real.pi^2/(M : ℝ)^2+64/(2 : ℝ)^payoffBits ≤ eps)
        (hgap : 2*(ν+64*(n : ℝ)/2^bits) < populationCDF p loss t)
        (hpop_above : q+eps+(ν+64*(n : ℝ)/2^bits) < populationCDF p loss t)
        (hpop_below : ∀ u : ℕ, u < v →
          populationCDF p loss (xs.getD u 0)+(ν+64*(n : ℝ)/2^bits) < q-eps)
        (hpop_den : 2*eps+(ν+64*(n : ℝ)/2^bits) < populationCDF p loss t),
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          ((closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind (fun ω =>
            riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
              (empiricalPrepare_unitary ω bits) hloss hM))
          (fun z => z.1 ≠ v ∨
            4*eps/(populationCDF p loss t-(ν+64*(n : ℝ)/2^bits))
              + 4*(ν+64*(n : ℝ)/2^bits)/populationCDF p loss t
              < |z.2.1-populationCVaR p loss t|)
          ≤ ENNReal.ofReal ((xs.length : ℝ)/(2*(N : ℝ)*ν^2)
              + (Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r)) := by
  intro n N p loss xs t ν hN hν hloss
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact empirical_tail_moment_sampling_bound p loss t ν hN hν hloss
  · exact empirical_uniform_tail_moment_sampling_bound p loss xs ν hN hν hloss
  · intro η ω hη hc hm hp hgap
    exact population_cvar_ratio_stability p loss t η ω hloss hη hc hm hp hgap
  · exact population_cvar_confidence_mass p loss xs ν hN hν hloss
  · intro bits payoffBits M r v q eps hM hxs hsorted hsupport hq0 hq1 heps hv ht hwindow
      hgap hpop_above hpop_below hpop_den
    classical
    have hprep : ∀ (ω : Fin N → Option (Fin n)) (t' : ℚ), t' ∈ xs →
        |riskCDF (empiricalPrepare ω bits) none loss t' - (empiricalCDF ω loss t' : ℝ)|
          ≤ 64*(n : ℝ)/2^bits := by
      intro ω t' ht'
      exact (empirical_actual_preparation_cdf_bias n N bits ω loss t' hN).2
    have hgood : ∀ (ω : Fin N → Option (Fin n)), ¬ badTable p loss xs ν ω →
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
            (empiricalPrepare_unitary ω bits) hloss hM)
          (fun z => z.1 ≠ v ∨
            4*eps/(populationCDF p loss t-(ν+64*(n : ℝ)/2^bits))
              + 4*(ν+64*(n : ℝ)/2^bits)/populationCDF p loss t
              < |z.2.1-populationCVaR p loss t|)
          ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) := by
      intro ω hω
      have hcdf : ∀ t' ∈ xs, |(empiricalCDF ω loss t' : ℝ) - populationCDF p loss t'| ≤ ν := by
        intro t' ht'
        by_contra hcon
        apply hω
        exact Or.inl ⟨t', ht', lt_of_not_ge hcon⟩
      have hmom : ∀ t' ∈ xs, |empiricalTailMoment ω loss t' - populationTailMoment p loss t'| ≤ ν := by
        intro t' ht'
        by_contra hcon
        apply hω
        exact Or.inr ⟨t', ht', lt_of_not_ge hcon⟩
      have htmem : t ∈ xs := by
        rw [← ht]
        rw [List.getD_eq_getElem xs 0 hv]
        exact List.getElem_mem hv
      have hcdf_t : |(empiricalCDF ω loss t : ℝ) - populationCDF p loss t| ≤ ν :=
        hcdf t htmem
      have hmom_t : |empiricalTailMoment ω loss t - populationTailMoment p loss t| ≤ ν :=
        hmom t htmem
      have hrisk_pop : |riskCDF (empiricalPrepare ω bits) none loss t
          - populationCDF p loss t| ≤ ν+64*(n : ℝ)/2^bits := by
        have h := abs_sub_le (riskCDF (empiricalPrepare ω bits) none loss t)
          (empiricalCDF ω loss t : ℝ) (populationCDF p loss t)
        have h1 := hprep ω t htmem
        have h2 := hcdf_t
        linarith
      have hden_actual : 2*eps < riskCDF (empiricalPrepare ω bits) none loss t := by
        have h := abs_le.mp hrisk_pop
        linarith [hpop_den]
      have habove_actual : q+eps < riskCDF (empiricalPrepare ω bits) none loss t := by
        have h := abs_le.mp hrisk_pop
        linarith [hpop_above]
      have hbelow_actual : ∀ u : ℕ, u < v →
          riskCDF (empiricalPrepare ω bits) none loss (xs.getD u 0) < q-eps := by
        intro u hu
        have hmem_u : xs.getD u 0 ∈ xs := by
          rw [List.getD_eq_getElem xs 0 (lt_trans hu hv)]
          exact List.getElem_mem (lt_trans hu hv)
        have h := abs_le.mp (hprep ω (xs.getD u 0) hmem_u)
        have h2 := abs_le.mp (hcdf (xs.getD u 0) hmem_u)
        linarith [hpop_below u hu]
      have hprep0 : 0 ≤ 64*(n : ℝ)/2^bits := by positivity
      have hmom' := hmom_t
      rw [show empiricalTailMoment ω loss t
        = (((∑ a, empiricalWeight ω a * riskTailPayoff loss t a) / (N : ℚ) : ℚ) : ℝ) from rfl]
        at hmom'
      have hcond := empiricalCVaR_target_error ω loss t
        (populationCDF p loss t) (populationTailMoment p loss t) ν eps xs q
        bits payoffBits M r v hN hloss hM hxs hsorted hsupport hq0 hq1 heps hv ht hwindow
        habove_actual hbelow_actual hden_actual hν.le hcdf_t hmom'
        (by have := hgap; linarith) hgap
      apply (risk_event_mono _ (fun z hz => ?_)).trans hcond
      rcases hz with hne | hbad
      · exact Or.inl hne
      · right
        have hlow : populationCDF p loss t - (ν+64*(n : ℝ)/2^bits)
            ≤ riskCDF (empiricalPrepare ω bits) none loss t := by
          have h := abs_le.mp hrisk_pop
          linarith
        have hpos : 0 < riskCDF (empiricalPrepare ω bits) none loss t := by
          linarith [hden_actual]
        have hden2 : 0 < populationCDF p loss t - (ν+64*(n : ℝ)/2^bits) := by
          have := hgap
          linarith
        have hfrac : 4*eps/riskCDF (empiricalPrepare ω bits) none loss t
            ≤ 4*eps/(populationCDF p loss t-(ν+64*(n : ℝ)/2^bits)) := by
          have hmul : (4*eps) * (populationCDF p loss t-(ν+64*(n : ℝ)/2^bits))
              ≤ (4*eps) * riskCDF (empiricalPrepare ω bits) none loss t :=
            mul_le_mul_of_nonneg_left hlow (by nlinarith [heps])
          rw [div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hden2]
          linarith
        rw [← show populationCVaR p loss t
          = populationTailMoment p loss t / populationCDF p loss t from rfl]
        exact lt_of_le_of_lt (add_le_add_left hfrac _) hbad
    have hbind := risk_bind_failure
      (closurePMF (independentSampleLaw (fun _ : Fin N => p)))
      (fun ω : Fin N → Option (Fin n) =>
        riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
          (empiricalPrepare_unitary ω bits) hloss hM)
      (badTable p loss xs ν)
      (fun z : ℕ × ℝ × ℕ => z.1 ≠ v ∨
        4*eps/(populationCDF p loss t-(ν+64*(n : ℝ)/2^bits))
          + 4*(ν+64*(n : ℝ)/2^bits)/populationCDF p loss t
          < |z.2.1-populationCVaR p loss t|)
      (ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r)) hgood
    rw [risk_closure_event (independentSampleLaw (fun _ : Fin N => p))
      (badTable p loss xs ν)] at hbind
    have hmass := population_cvar_bad_mass p loss xs ν hN hν hloss
    calc
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          ((closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind (fun ω =>
            riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
              (empiricalPrepare_unitary ω bits) hloss hM))
          (fun z => z.1 ≠ v ∨
            4*eps/(populationCDF p loss t-(ν+64*(n : ℝ)/2^bits))
              + 4*(ν+64*(n : ℝ)/2^bits)/populationCDF p loss t
              < |z.2.1-populationCVaR p loss t|)
        ≤ ENNReal.ofReal (Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p))
              (badTable p loss xs ν))
            + ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) := hbind
      _ ≤ ENNReal.ofReal ((xs.length : ℝ)/(4*(N : ℝ)*ν^2)
              + (xs.length : ℝ)/(4*(N : ℝ)*ν^2))
            + ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) := by
        exact add_le_add (ENNReal.ofReal_le_ofReal hmass) le_rfl
      _ = ENNReal.ofReal ((xs.length : ℝ)/(2*(N : ℝ)*ν^2)
              + (Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) := by
        have hring : (xs.length : ℝ)/(4*(N : ℝ)*ν^2) + (xs.length : ℝ)/(4*(N : ℝ)*ν^2)
              + ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r)
            = (xs.length : ℝ)/(2*(N : ℝ)*ν^2)
              + (Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r := by ring
        rw [← hring]
        exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- Collects exact and sample quantile crossing properties, separation based recovery,
population CDF approximation, and impossibility of perfect finite sample discrimination for
the specified nearby populations. -/
theorem clause23_endpoint :
    ∀ (n N : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
      (xs : List ℚ) (q ν : ℝ) (hN : 0 < N) (hν : 0 < ν),

      (∀ u, u < exactVaRIndex p loss xs q → populationCDF p loss (xs.getD u 0) < q) ∧
      (exactVaRIndex p loss xs q < xs.length →
        q ≤ populationCDF p loss (xs.getD (exactVaRIndex p loss xs q) 0)) ∧

      (∀ (ω : Fin N → Option (Fin n)) (u : ℕ),
        u < sampleVaRIndex ω loss xs q → (empiricalCDF ω loss (xs.getD u 0) : ℝ) < q) ∧
      (∀ (ω : Fin N → Option (Fin n)), sampleVaRIndex ω loss xs q < xs.length →
        q ≤ (empiricalCDF ω loss (xs.getD (sampleVaRIndex ω loss xs q) 0) : ℝ)) ∧

      (exactVaRGap p loss xs q ν →
        FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
          sampleVaRIndex ω loss xs q ≠ exactVaRIndex p loss xs q)
          ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2)) ∧

      (∀ (ω : Fin N → Option (Fin n)) (η : ℝ) (hη : 0 ≤ η),
        cdfGood p loss xs η ω → sampleVaRIndex ω loss xs q < xs.length →
        q - η ≤ populationCDF p loss (xs.getD (sampleVaRIndex ω loss xs q) 0) ∧
        (∀ u, u < sampleVaRIndex ω loss xs q →
          populationCDF p loss (xs.getD u 0) < q + η)) ∧

      (∀ (bits : ℕ) (ω : Fin N → Option (Fin n)), cdfGood p loss xs ν ω →
        ∀ t ∈ xs,
          |riskCDF (empiricalPrepare ω bits) none loss t - populationCDF p loss t|
            ≤ ν + 64*(n : ℝ)/2^bits) ∧

      (∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
        (alg : (Fin N → Option (Fin 2)) → ℕ),
        ¬ (FinDist.probEvent (L := N) noGapPop (fun ω : Fin N → Option (Fin 2) =>
              alg ω = 0) = 1 ∧
            FinDist.probEvent (L := N) (nearPop ε hε hε1) (fun ω : Fin N → Option (Fin 2) =>
              alg ω = 1) = 1)) ∧

      (FinDist.probEvent (L := N) noGapPop (fun ω : Fin N → Option (Fin 2) =>
        sampleVaRIndex ω twoAtomLoss [0, 1] (1/2) = 0) < 1) := by
  intro n N p loss xs q ν hN hν
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (exactVaRIndex_spec p loss xs q).2
  · exact (exactVaRIndex_spec p loss xs q).1
  · intro ω u hu
    exact (sampleVaRIndex_spec ω loss xs q).2 u hu
  · intro ω hvlt
    exact (sampleVaRIndex_spec ω loss xs q).1 hvlt
  · intro hgap
    exact exactVaR_recovery_bound p loss xs q ν hN hν hgap
  · intro ω η hη hgood hvlt
    exact sampleVaRIndex_population_bounds_of_good p loss xs q η ω hgood hvlt
  · intro bits ω hgood t ht
    exact prepared_cdf_transport p loss xs ν ω hN hgood t ht
  · intro ε hε hε1 alg
    exact exactVaR_no_procedure_exact_under_both ε hε hε1 alg
  · exact sampleVaRIndex_success_lt_one hN

/-- Combines finite grid crossing specifications, quantile rounding error, sampling confidence,
conditional mean window deviation, and quantile uniqueness under the stated hypotheses. -/
theorem clause25_quantization_interface :
    ∀ (n N : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℝ)
      (Δ q ν : ℝ) (iT : ℕ) (t : ℝ),
      0 < N → 0 < Δ → 0 < q → 0 < ν → (∀ a, 0 ≤ loss a ∧ loss a ≤ 1) →
      q ≤ marketCDF p loss (gridThreshold Δ iT) →
      marketVaRAt p loss q t →
      (marketGridIndex p loss Δ q iT ≤ iT ∧
        q ≤ marketCDF p loss (gridThreshold Δ (marketGridIndex p loss Δ q iT)) ∧
        (∀ j : ℕ, j < marketGridIndex p loss Δ q iT →
          marketCDF p loss (gridThreshold Δ j) < q)) ∧
      |gridThreshold Δ (marketGridIndex p loss Δ q iT) - t| ≤ Δ ∧
      (∀ (ω : Fin N → Option (Fin n)),
        (marketGridRecordIndex ω loss Δ q iT ≤ iT ∧
          q ≤ marketEmpiricalCDF ω loss
            (gridThreshold Δ (marketGridRecordIndex ω loss Δ q iT))) ∨
        (marketGridRecordIndex ω loss Δ q iT = iT + 1 ∧
          ∀ j : ℕ, j ≤ iT →
            marketEmpiricalCDF ω loss (gridThreshold Δ j) < q)) ∧
      (FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
          ∃ j : Fin (iT+1),
            ν < |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
              - marketCDF p loss (gridThreshold Δ j.1)|)
        ≤ ((iT+1 : ℝ))/(4*(N : ℝ)*ν^2)) ∧
      (∀ (g : ℝ), t ≤ g → 0 < marketCDF p loss t → 0 < marketCDF p loss g →
        marketCVaR p loss g - marketCVaR p loss t
          ≤ (marketCDF p loss g - marketCDF p loss t) / marketCDF p loss g) ∧
      (∀ (t' : ℝ), marketVaRAt p loss q t' → t' = t) := by
  intro n N p loss Δ q ν iT t hN hΔ hq hν hloss hcap hv
  refine ⟨marketGridIndex_spec p loss Δ q iT hcap, ?_, ?_, ?_, ?_, ?_⟩
  · exact marketGrid_quantization p loss Δ q iT t (fun a => (hloss a).1) hΔ hq hcap hv
  · intro ω
    exact marketGridRecordIndex_spec ω loss Δ q iT
  · exact marketGrid_uniform_sampling_bound p loss Δ ν iT hN hν
  · intro g htg hFt hFg
    exact marketCVaR_window_deviation p loss hloss htg hFt hFg
  · intro t' hv'
    by_contra hcon
    push Not at hcon
    rcases lt_or_gt_of_ne hcon with hlt | hgt
    · exact (marketVaRAt_unique p loss hv' hv hlt).elim
    · exact (marketVaRAt_unique p loss hv hv' hgt).elim

/-- Gives exact market program sample, comparison, amplitude record, query, and gate accounting
together with the grid scan bound. -/
theorem clause25_cost_interface :
    ∀ (n N : ℕ) (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ)
      (Δ ν : ℝ) (iT M r : ℕ),
      (marketProgramResources M r ω loss Δ ν iT).samples = N ∧
      (marketProgramResources M r ω loss Δ ν iT).tableReads ≤ iT + 1 ∧
      (marketProgramResources M r ω loss Δ ν iT).recordComparisons
        = (marketProgramResources M r ω loss Δ ν iT).tableReads * N ∧
      (marketProgramResources M r ω loss Δ ν iT).aeRecords
        = (marketProgramResources M r ω loss Δ ν iT).tableReads * (2*r+1) ∧
      (marketProgramResources M r ω loss Δ ν iT).queries
        = (marketProgramResources M r ω loss Δ ν iT).aeRecords * (M-1) ∧
      (marketProgramResources M r ω loss Δ ν iT).gates
        = (marketProgramResources M r ω loss Δ ν iT).aeRecords * (5*(M-1)+3) := by
  intro n N ω loss Δ ν iT M r
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  exact marketGridScan_le ω loss Δ ν iT

/-- Combines pointwise loading error, regularity based CDF bias, uniform grid confidence,
resource bounds, and a necessary sample budget under the stated window regularity
hypotheses. -/
theorem clause25_endpoint :
    ∀ (n N : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℝ)
      (ρ Δ ν : ℝ) (iT bits k M r : ℕ),
      0 < N → 0 < ν → 0 ≤ ρ →
      marketWindowRegular p loss ρ k →
      (∀ ω : Fin N → Option (Fin n),
        marketQuantumWindowRegular (empiricalPrepare ω bits) none loss ρ k) →
      (∀ (a : Option (Fin n)) (t : ℝ),
        |marketLoadedIndicator loss k t a - marketIndicator loss t a|
          ≤ marketWindowIndicator loss k t a) ∧
      (∀ (t : ℝ),
        |marketLoadedCDF p loss k t - marketCDF p loss t|
          ≤ ρ * 2 * (1/2 : ℝ)^k) ∧
      (∀ (ω : Fin N → Option (Fin n)) (t : ℝ),
        |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k t
            - marketQuantumCDF (empiricalPrepare ω bits) none loss t|
          ≤ marketQuantumWindowMass (empiricalPrepare ω bits) none loss k t) ∧
      (FinDist.probEvent (L := N) p
        (fun ω : Fin N → Option (Fin n) =>
          ∃ i : Fin (iT+1),
            ρ * 2 * (1/2 : ℝ)^k + 64*(n : ℝ)/2^bits + ν
              < |marketQuantumLoadedCDF (empiricalPrepare ω bits) none loss k
                    (gridThreshold Δ i.1) - marketCDF p loss (gridThreshold Δ i.1)|)
        ≤ (iT + 1) / (4*(N : ℝ)*ν^2)) ∧
      (∀ (ω : Fin N → Option (Fin n)),
        (marketProgramResources M r ω loss Δ ν iT).tableReads ≤ iT + 1 ∧
        (marketProgramResources M r ω loss Δ ν iT).aeRecords
          ≤ (iT + 1) * (2*r+1)) ∧
      (∀ (δ : ℝ) (N : ℕ), 0 < δ → 0 < N →
        (iT + 1) / (4*(N : ℝ)*ν^2) ≤ δ →
        (iT + 1) / (4*δ*ν^2) ≤ (N : ℝ)) := by
  intro n N p loss ρ Δ ν iT bits k M r hN hν hρ hReg hRegQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a t
    exact marketIndicator_diff_le loss k t a
  · intro t
    exact marketLoadedCDF_deviation_le p loss ρ k t hReg
  · intro ω t
    exact marketQuantumLoadedCDF_deviation (empiricalPrepare ω bits) none loss k t
  · exact marketHeadline_uniform p bits k loss ρ Δ iT ν hN hν hρ hRegQ
  · intro ω
    exact marketHeadline_resources M r ω loss Δ ν iT
  · intro δ N hδ hN hbound
    exact marketHeadline_sampling_budget hδ hν N hN hbound

/-- Collects signed loading and phase approximation guarantees, numerator and greatest common
divisor bounds, attainable workspace schedules, and sound emitter decisions with a bounded
rejection window. -/
theorem clause24_endpoint :
    ∀ (k L : ℕ) (θ : ℝ),

      ((loadReal k θ : ℝ) ≤ θ ∧ |(loadReal k θ : ℝ) - θ| < (1/2 : ℝ)^k ∧
        (θ < 0 → (loadReal k θ : ℝ) < 0)) ∧

      (‖Rz θ - Rz (((solvePhase k θ : ℝ)))‖ ≤ (1/2 : ℝ)^k) ∧

      (riskPhaseGate k θ ∈ Matrix.unitaryGroup Bool ℂ ∧
        (∃ gs : List (ReflectionGate 1), GateCount (reflectionCompile gs) = 1 ∧
          QueryCount (reflectionCompile gs) = 0) ∧
        (|θ| ≤ 1 → ‖riskPhaseGate k θ - Rz θ‖ ≤ 2 * (1/2 : ℝ)^k)) ∧

      (∀ (x : ℝ), |x| ≤ (L : ℝ) →
        |(loadNumerator k x : ℝ)| < (2 : ℝ)^loadBitCost k L) ∧

      (∀ (x : ℝ), |x| ≤ (L : ℝ) →
        euclidGcd (euclidStepBound (emitterScale k L))
          ((loadNumerator k x).natAbs) (2 ^ k)
            = Nat.gcd ((loadNumerator k x).natAbs) (2 ^ k)) ∧

      (∀ (e : ℕ), ∃ S : SpaceSchedule, S.wordLen = loadBitCost k L ∧ S.events = e ∧
        SpaceSchedule.Correct S ∧ S.peakSpace = loadBitCost k L * (e - 1)) ∧

      ((riskEmitter k θ (0 : ℚ)).threshold = loadReal k θ ∧
        (riskEmitter k θ (0 : ℚ)).reduction
          = Nat.gcd ((loadNumerator k θ).natAbs) (2 ^ k) ∧
        |((riskEmitter k θ (0 : ℚ)).threshold : ℝ) - θ| < (1/2 : ℝ)^k) ∧

      ((∀ (readout : ℚ), (riskEmitter k θ readout).decision = true →
          (readout : ℝ) ≤ θ) ∧
        (∀ (readout : ℚ), (riskEmitter k θ readout).decision = false →
          (readout : ℝ) ≤ θ → (loadReal k θ : ℝ) < (readout : ℝ) ∧
            (readout : ℝ) - (loadReal k θ : ℝ) < (1/2 : ℝ)^k)) := by
  intro k L θ
  refine ⟨⟨loadReal_le k θ, loadReal_error k θ, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hθ
    exact loadReal_neg k hθ
  · exact solvePhase_phase_error k θ
  · refine ⟨riskPhaseGate_unitary k θ, ?_, ?_⟩
    · exact riskPhaseGate_fixed_gate_ledger k θ
    · intro hθ
      exact riskPhaseGate_error k θ hθ
  · intro x hx
    exact loadNumerator_bits_lt k L hx
  · intro x hx
    exact riskEmitter_gcd k L hx
  · intro e
    exact emitter_peakSpace_le k L e
  · refine ⟨riskEmitter_threshold k θ 0, ?_, ?_⟩
    · exact riskEmitter_reduction k
    · exact riskEmitter_threshold_error k θ 0
  · refine ⟨?_, ?_⟩
    · intro readout hdec
      exact riskEmitter_decision_sound k readout hdec
    · intro readout hdec hreadout
      exact riskEmitter_decision_window k readout hdec hreadout

end Qatlib.Concepts.RiskEstimation.PopulationGap
