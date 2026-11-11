/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RecordedMedianProgram
import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalQuan

/-!
# Recorded median estimation of risk CDFs

This module expresses a rational loss threshold indicator as a payoff and proves that its Born
weighted expectation is the risk CDF. Its variance is at most one quarter for unitary
preparation, enabling a recorded median estimator in the quantum Monte Carlo framework of
[Montanaro2015].

`frontier1` combines an exponentially decreasing median failure bound with explicit comparison,
bit time, storage, output size, and query accounting.

## Main statements

* `riskCDFPayoffRat_sum`: the indicator expectation is the risk CDF.
* `riskCDFPayoffRat_variance`: the one quarter variance bound.
* `frontier1`: confidence and resource guarantees for recorded median readout.

## References

* [Montanaro, 2015][Montanaro2015]
* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.output1
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeSearch.NativeMean
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib
open Matrix
open scoped Classical BigOperators
set_option warningAsError false

/-- The rational indicator that outcome `i` has loss at most threshold `t`. -/
def riskCDFPayoffRat {I : Type} (loss : I → ℚ) (t : ℚ) (i : I) : ℚ :=
  if loss i ≤ t then 1 else 0

/-- Casting the rational CDF payoff to the reals gives the existing real risk CDF payoff. -/
theorem riskCDFPayoffRat_cast {I : Type} (loss : I → ℚ) (t : ℚ) (i : I) :
    ((riskCDFPayoffRat loss t i : ℚ) : ℝ)
      = Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDFPayoff loss t i := by
  unfold riskCDFPayoffRat Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDFPayoff
  split
  · norm_num
  · norm_num

/-- The Born weighted expectation of the rational indicator equals `riskCDF A j loss t`. -/
theorem riskCDFPayoffRat_sum {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) :
    (∑ i, BornProb (A *ᵥ Ket j) i*(riskCDFPayoffRat loss t i : ℝ))
      = Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDF A j loss t := by
  rw [Qatlib.Concepts.RiskEstimation.CDFEstimation.riskCDF_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [riskCDFPayoffRat_cast]

/-- The rational CDF payoff takes only the values zero and one. -/
theorem riskCDFPayoffRat_zero_or_one {I : Type} (loss : I → ℚ) (t : ℚ) (i : I) :
    riskCDFPayoffRat loss t i = 0 ∨ riskCDFPayoffRat loss t i = 1 := by
  unfold riskCDFPayoffRat
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Under unitary preparation, the Born weighted variance of the CDF indicator is at most `(1 /
2) ^ 2`. -/
theorem riskCDFPayoffRat_variance {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ i, BornProb (A *ᵥ Ket j) i*
        ((riskCDFPayoffRat loss t i : ℝ)
          -(∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ)))^2)
      ≤ (1/2 : ℝ)^2 := by
  have hn : (∑ i, BornProb (A *ᵥ Ket j) i) = 1 :=
    normalized_applyGate hA (normalized_ket j)
  have hx01 : ∀ i, (riskCDFPayoffRat loss t i : ℝ) = 0 ∨
      (riskCDFPayoffRat loss t i : ℝ) = 1 := by
    intro i
    rcases riskCDFPayoffRat_zero_or_one loss t i with h | h
    · exact Or.inl (by rw [h]; push_cast; rfl)
    · exact Or.inr (by rw [h]; push_cast; rfl)
  have hxnn : ∀ i, 0 ≤ (riskCDFPayoffRat loss t i : ℝ) ∧
      (riskCDFPayoffRat loss t i : ℝ) ≤ 1 := by
    intro i
    rcases hx01 i with h | h <;> rw [h] <;> norm_num
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ,
      μ = ∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ) :=
    ⟨_, rfl⟩
  rw [← hμdef]
  have hμ0 : 0 ≤ μ := by
    rw [hμdef]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (bornProb_nonneg _ _) (hxnn i).1
  have hμ1 : μ ≤ 1 := by
    rw [hμdef]
    calc ∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ)
        ≤ ∑ i', BornProb (A *ᵥ Ket j) i'*1 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hxnn i).2 (bornProb_nonneg _ _)
      _ = 1 := by rw [Finset.sum_congr rfl (fun i _ => mul_one _), hn]
  have hxx : ∀ i, BornProb (A *ᵥ Ket j) i*((riskCDFPayoffRat loss t i : ℝ)*
        (riskCDFPayoffRat loss t i : ℝ))
      = BornProb (A *ᵥ Ket j) i*(riskCDFPayoffRat loss t i : ℝ) := by
    intro i
    rcases hx01 i with h | h <;> rw [h] <;> norm_num
  have hexp : ∀ i, BornProb (A *ᵥ Ket j) i*
        ((riskCDFPayoffRat loss t i : ℝ)-μ)^2
      = BornProb (A *ᵥ Ket j) i*((riskCDFPayoffRat loss t i : ℝ)*
          (riskCDFPayoffRat loss t i : ℝ))
        - 2*μ*(BornProb (A *ᵥ Ket j) i*(riskCDFPayoffRat loss t i : ℝ))
        + μ*μ*(BornProb (A *ᵥ Ket j) i) := fun i => by ring
  have hsplit : (∑ i, BornProb (A *ᵥ Ket j) i*((riskCDFPayoffRat loss t i : ℝ)-μ)^2)
      = (∑ i, BornProb (A *ᵥ Ket j) i*((riskCDFPayoffRat loss t i : ℝ)*
            (riskCDFPayoffRat loss t i : ℝ)))
        - 2*μ*(∑ i, BornProb (A *ᵥ Ket j) i*(riskCDFPayoffRat loss t i : ℝ))
        + μ*μ*(∑ i, BornProb (A *ᵥ Ket j) i) := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hexp i),
      Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hsplit, hn, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hxx i), hμdef]
  have hring : (∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))
      - 2*(∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))
        *(∑ i, BornProb (A *ᵥ Ket j) i*(riskCDFPayoffRat loss t i : ℝ))
      + (∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))
        *(∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))*1
      = (∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))
        - (∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ))
        *(∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ)) := by ring
  rw [hring, show (1/2 : ℝ)^2 = 1/4 by norm_num]
  nlinarith [sq_nonneg
    (∑ i', BornProb (A *ᵥ Ket j) i'*(riskCDFPayoffRat loss t i' : ℝ) - 1/2)]

namespace output2

/-- For unitary preparation and `k ≥ 4`, the recorded median estimates the risk CDF within `9 *
(1 / 2) * (1 / 2) ^ k` except with probability at most `(143 / 144) ^ r`. It also gives
explicit comparison, bit time, storage, output bit size, and per anchor query guarantees. -/
theorem frontier1 :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (j : I) (loss : I → ℚ) (t : ℚ) (k r : ℕ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ), 4 ≤ k →
      let f := riskCDFPayoffRat loss t
      let hP : ∀ (x : I) (l : Fin (k+2)), nativeLayerPrepare A
          (fun i => max 0 ((f i-f x)/(4*(1/2:ℚ)))) k l ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
        fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f i-f x)/(4*(1/2:ℚ)))) k l.val hA (fun _ => le_max_left _ _)
      let hN : ∀ (x : I) (l : Fin (k+2)), nativeLayerPrepare A
          (fun i => max 0 ((f x-f i)/(4*(1/2:ℚ)))) k l ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
        fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f x-f i)/(4*(1/2:ℚ)))) k l.val hA (fun _ => le_max_left _ _)
      let law := nativeSignedLaw A j f (1/2) k hA hP hN
      let B := nativeTrialBits f (1/2) k
      ((∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ))
        = Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDF A j loss t ∧
      law.probEvent (fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
        9*((1/2 : ℚ):ℝ)*(1/2 : ℝ)^k <
          |((recordedMedianProgram r
              (List.ofFn (fun z => nativeSignedOutput f (1/2) k (ω z)))).1 : ℝ)
            -Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDF A j loss t|)
        ≤ (143/144 : ℝ)^r ∧
      (∀ (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)),
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f (1/2) k (ω z)))).2.1
          ≤ (2*r+1)*(2*r+1) ∧
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f (1/2) k (ω z)))).2.2
          = 2*r+1 ∧
        recordedMedianBitTime r B (List.ofFn (fun z => nativeSignedOutput f (1/2) k (ω z)))
          ≤ (2*r+1)*(2*r+1)*ratCompareBitCost B ∧
        (recordedMedianProgram r (List.ofFn (fun z => nativeSignedOutput f (1/2) k (ω z)))).2.2 * B
          + ratCompareRegisterBits B + ratCounterBits (2*r+1)
          = recordedMedianPeakBits (2*r+1) B) ∧
      (∀ z : I × (LayerRecord k × LayerRecord k),
        ratBits (nativeSignedOutput f (1/2) k z) ≤ B) ∧
      (∀ x : I, ((nativeSignedAEPrograms A j f (1/2) k x).map QueryCount).sum =
        2*(k+2)*(2*layerRepetitions k+1)*(layerGrid k-1))) := by
  intro I _ _ A j loss t k r hA hk f hP hN law B
  have hσ : (0:ℚ) < 1/2 := by norm_num
  have hvar : (∑ i, BornProb (A *ᵥ Ket j) i*
      ((f i : ℝ)-(∑ i', BornProb (A *ᵥ Ket j) i'*(f i' : ℝ)))^2) ≤ ((1/2 : ℚ):ℝ)^2 := by
    have h := riskCDFPayoffRat_variance A j loss t hA
    have hcσ : ((1/2 : ℚ):ℝ) = (1/2:ℝ) := by norm_num
    rw [hcσ]
    exact h
  obtain ⟨hfail, hres, hbits, hledger⟩ :=
    output1.frontier1 I A j f (1/2) k r hA hk hσ hvar
  have he : (∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ))
      = Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018.riskCDF A j loss t :=
    riskCDFPayoffRat_sum A j loss t
  refine ⟨he, ?_, hres, hbits, hledger⟩
  simpa only [he] using! hfail

end output2

end Qatlib.Concepts.RiskEstimation.PopulationGap
