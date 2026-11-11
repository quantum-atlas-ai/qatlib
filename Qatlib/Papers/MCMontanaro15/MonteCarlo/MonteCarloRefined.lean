/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloRefinedDefs

/-!
# Refined Monte Carlo truncation and resource bounds

This module assembles finite-law identities and estimates used in quantum
Monte Carlo analysis: truncation bias and second-moment tails, centered
variance, band-mean reconstruction, pilot-certified median budgets, and
partition-function and walk ledgers. Each endpoint states its required
positivity, logarithm-domain, or supplied-estimator hypotheses explicitly.

The source framework is [Montanaro2015]. Exact constants and the bit, memory,
and stopping ledgers refer to the local models.
-/
set_option warningAsError false
open Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloRefined
namespace StageBMONTECARLO

open Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic.StageBMONTECARLO
open Qatlib.Papers.MCMontanaro15.MonteCarlo.StageBMONTECARLO
open Qatlib
open scoped BigOperators ComplexOrder

variable {X : Type} [Fintype X] [DecidableEq X]
variable (n₀ : ℕ)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Combines the partition-limit comparison, exponential tail and reflection-error identity with
the explicit Theorem 11 walk, reflection, and copy cost expressions. -/
theorem clause51_endpoint {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (l : WalkLedger)
    (hR : 0 < l.reflections) (hg : 0 ≤ l.gamma) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    partitionFnLimit H ≤ partitionFn H l.gamma ∧
      (l.reflections : ℝ) * (l.gamma / l.reflections) + l.gamma = 2 * l.gamma ∧
      0 ≤ partitionFn H l.gamma - partitionFnLimit H ∧
        partitionFn H l.gamma - partitionFnLimit H
          ≤ (Fintype.card Ω : ℝ) * Real.exp (-l.gamma) ∧
      theorem11WalkSteps l ε δ
        = ((l.schedule : ℝ) ^ 2 * Real.sqrt (l.relaxation : ℝ) / ε)
          * Real.log (l.schedule / ε) ^ 5 * Real.log (l.schedule / δ)
            * Real.log (Real.log (l.schedule / ε)) ∧
      (l.schedule : ℝ) * theorem11Reflections l ε
        = (l.schedule : ℝ) * (l.schedule / ε * Real.log (l.schedule / ε) ^ 3
            * Real.log (Real.log (l.schedule / ε))) ∧
      (l.schedule : ℝ) * theorem11Copies l ε
        = (l.schedule : ℝ)
          * (Real.log (l.schedule / ε) * Real.log (Real.log (l.schedule / ε))) := by
  have hgap := partitionFn_sub_partitionFnLimit_le H l.gamma hg
  exact ⟨partitionFnLimit_le_partitionFn H l.gamma, clause51_walk_state_error l hR,
    hgap.1, hgap.2, rfl, rfl, rfl⟩

/-- Truncation bias is exactly the expectation in the discarded tail, the
decomposition used in [Montanaro, Monte Carlo estimation][Montanaro2015]. -/
theorem clause52_truncation_error {X : Type} [Fintype X] (p : FinDist X) (f : X → ℝ)
    (k : ℕ) :
    p.expect f - truncatedExpectation p f k = tailAbove p f (truncationThreshold k) := by
  unfold truncatedExpectation tailAbove truncationThreshold
  simp only [FinDist.expect]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (2 : ℝ) ^ k ≤ f x
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- The truncation error equals the upper-tail contribution and satisfies its second-moment
bound. For B ≥ 1, the reciprocal lies in (0, 1], and the same bound holds after adding the
layer error. -/
theorem clause52_endpoint (p : FinDist X) (f : X → ℝ) (k : ℕ) (γ : ℝ) (B : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k) (hB : 1 ≤ B) :
    p.expect f - truncatedExpectation p f k = tailAbove p f (truncationThreshold k) ∧
      tailAbove p f (truncationThreshold k)
        ≤ p.expect (fun x => f x ^ 2) / truncationThreshold k ∧
      (0 < 1 / B ∧ 1 / B ≤ 1) ∧
      tailAbove p f ((2 : ℝ) ^ k) + 2 * γ * (k : ℝ)
        ≤ p.expect (fun x => f x ^ 2) / (2 : ℝ) ^ k + 2 * γ * (k : ℝ) := by
  exact ⟨clause52_truncation_error p f k,
    tailAbove_le_secondMoment_div p f hf (truncationThreshold k) hm,
    clause52_overlap_domain B hB, clause52_error_ledger p f k γ hf hm⟩

/-- Collects the exact threshold for 1/9 + 2δ ≤ 3/10, the transport and printed baseline
identities, their complementary success expression, and the sum 1/9 + 2/9 = 1/3. -/
theorem clause53_endpoint (δ : ℝ) (T : ℕ) (γ : ℝ) :
    ((1 : ℝ) / 9 + 2 * δ ≤ 3 / 10 ↔ δ ≤ 17 / 180) ∧
      sourceLemma18Transport T γ = (T : ℝ) * (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ ∧
      sourceLemma18Baseline T γ
        = 3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ ∧
      1 - sourceLemma18Baseline T γ
        = 7 / 10 - (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ ∧
      (1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) = 1 / 3 := by
  exact ⟨(clause53_sourcePrintedThreeTenths δ).1, clause53_transport_ledger T γ,
    clause53_baseline_split T γ, (clause53_sourceSuccessRate T γ).1,
    (clause53_sourcePrintedThreeTenths (1 / 9)).2.1⟩

/-- For positive σ and ε with log(σ/ε) > 1, the iterated logarithm log(log(σ/ε)) is positive. -/
theorem clause54_parameter_domain {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    (hlog : 1 < Real.log (σ / ε)) :
    0 < σ ∧ 0 < ε ∧ 1 < Real.log (σ / ε) ∧ 0 < Real.log (Real.log (σ / ε)) := by
  have hpos : 0 < Real.log (σ / ε) := lt_trans (by norm_num) hlog
  refine ⟨hσ, hε, hlog, ?_⟩
  exact Real.log_pos hlog

/-- Under the positive logarithm domain and band-mean error bounds, combines reconstruction
error at most 8σε with the 2/3 success arithmetic, explicit Theorem 5 costs, and seven-copy
ledger identity. -/
theorem clause54_endpoint (p : FinDist X) (f : X → ℝ) (σ m muNeg muPos ε : ℝ)
    (hσ : 0 < σ) (hε : 0 < ε) (hlog : 1 < Real.log (σ / ε))
    (hneg : |bandMeanBelow p f σ m - muNeg| ≤ ε)
    (hpos : |bandMeanAbove p f σ m - muPos| ≤ ε) :
    |algorithm3Output σ m muNeg muPos - p.expect (fun i => f i)| ≤ 8 * σ * ε ∧
      1 - ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9)) = 2 / 3 ∧
      (0 < σ ∧ 0 < ε ∧ 1 < Real.log (σ / ε) ∧ 0 < Real.log (Real.log (σ / ε))) ∧
      theorem5Copies σ ε = Real.log (σ / ε) * Real.log (Real.log (σ / ε)) ∧
      theorem5Reflections σ ε
        = (σ / ε) * Real.log (σ / ε) ^ 3 * Real.log (Real.log (σ / ε)) ∧
      (CostLedger.replicate ({ copies := 1 + 2 * 3, reflections := 2 * 3, medians := 2 * 3, classicalBits := 0 } : CostLedger) 1).copies = 7 := by
  refine ⟨clause54_algorithm3_error_ledger p f σ m muNeg muPos ε hσ hneg hpos,
    (clause54_algorithm3_success (1 / 9) (by norm_num)).2,
    clause54_parameter_domain hσ hε hlog, rfl, rfl, rfl⟩

/-- For nonzero σ, scaling a payoff by 1/σ and shifting by m divides its variance by σ². -/
theorem clause55_centered_variance {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (σ m : ℝ) (hσ : σ ≠ 0) :
    p.variance (fun x => f x / σ - m) = p.variance f / σ ^ 2 := by
  have hexp : p.expect (fun x => f x / σ - m) = p.expect f / σ - m := by
    have h1 : (∑ x, p.prob x * (f x / σ - m))
        = (∑ x, p.prob x * (f x / σ)) - (∑ x, p.prob x * m) := by
      calc (∑ x, p.prob x * (f x / σ - m))
          = ∑ x, (p.prob x * (f x / σ) - p.prob x * m) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ = (∑ x, p.prob x * (f x / σ)) - (∑ x, p.prob x * m) := by
            rw [← Finset.sum_sub_distrib]
    have h2 : (∑ x, p.prob x * (f x / σ)) = p.expect f / σ := by
      rw [FinDist.expect]
      exact expect_div_const p f σ
    have h3 : (∑ x, p.prob x * m) = m * (∑ x, p.prob x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [FinDist.expect]
    rw [h1, h2, h3, p.sum_one, mul_one]
  have hsq : ∀ x : X,
      (f x / σ - m - (p.expect f / σ - m)) = (f x - p.expect f) / σ := by
    intro x
    have h1 : f x / σ - m - (p.expect f / σ - m) = f x / σ - p.expect f / σ := by ring
    rw [h1]
    field_simp [hσ]
  have hmain : p.expect (fun x => (f x / σ - m - (p.expect f / σ - m)) ^ 2)
      = p.expect (fun x => ((f x - p.expect f) / σ) ^ 2) := by
    rw [FinDist.expect]
    apply Finset.sum_congr rfl
    intro x _
    rw [hsq]
  have hdiv : p.expect (fun x => ((f x - p.expect f) / σ) ^ 2)
      = p.expect (fun x => (f x - p.expect f) ^ 2) / σ ^ 2 := by
    rw [FinDist.expect]
    calc (∑ x, p.prob x * (((f x - p.expect f) / σ) ^ 2))
        = ∑ x, (p.prob x * (f x - p.expect f) ^ 2) / σ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [div_pow]
          ring
      _ = (∑ x, p.prob x * (f x - p.expect f) ^ 2) / σ ^ 2 := by
            rw [← Finset.sum_div]
  unfold FinDist.variance
  rw [hexp, hmain, hdiv]

/-- Combines the two-level opaque-sampler obstruction, pilot variance and concentration bounds,
certified sample-size identity, and variance bound for a payoff bounded by one. It also
gives the variance formula for every nonzero scaling centered at the scaled mean. -/
theorem clause55_endpoint (alg : OpaqueSampler) (law : FinDist X) (f : X → ℝ)
    (ω : DrawRecord n₀ X) (t : ℝ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hdraw : (1 - p) ^ alg.draws > 1 / 3)
    (hn₀ : 0 < n₀) (ht : 0 < t) (hf : ∀ x, |f x| ≤ 1)
    (hgood : |pilotSecondMoment f ω - law.expect (fun x => f x ^ 2)| ≤ t) :
    (∃ N : ℕ, 0 < N ∧
      (twoLevelLaw p (le_of_lt hp) hp1 N).probEvent
          (fun ω : Fin alg.draws → Fin (N + 2) =>
            1 / 4 < |alg.run (fun k => (ω k).val) - p * (N + 1)|) > 1 / 3) ∧
      ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) = 1 / 3) ∧
      law.variance f ≤ pilotVarianceBound f t ω ∧
      certifiedSamplesPerGroup f t 1 ω = Nat.ceil (4 * (pilotSecondMoment f ω + t) / 1 ^ 2) ∧
      law.probEvent (L := n₀) (fun ω : DrawRecord n₀ X =>
        t < |pilotSecondMoment f ω - law.expect (fun x => f x ^ 2)|)
        ≤ 1 / (n₀ * t ^ 2) ∧
      law.variance f ≤ 1 ∧
      (∀ σ' : ℝ, σ' ≠ 0 →
        law.variance (fun x => f x / σ' - law.expect f / σ')
          = law.variance f / σ' ^ 2) := by
  refine ⟨clause55_no_go_two_level alg p hp hp1 hdraw,
    (clause53_sourcePrintedThreeTenths (1 / 9)).2.1,
    clause56_pilot_certifies_variance law f ω t hgood, rfl,
    clause56_pilot_certificate law f hn₀ hf t ht,
    clause56_variance_le_one_of_bounded law f hf,
    fun σ' hσ' => clause55_centered_variance law f σ' (law.expect f / σ') hσ'⟩

/-- For a nonnegative payoff with the stated second-moment bound, the truncation error equals
the upper tail, this tail is at most ε, and the variance is at most the second moment. -/
theorem clause56_endpoint (p : FinDist X) (f : X → ℝ) (k : ℕ) (ε : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k)
    (hbound : p.expect (fun x => f x ^ 2) ≤ (2 : ℝ) ^ k * ε) :
    p.expect f - truncatedExpectation p f k = tailAbove p f (truncationThreshold k) ∧
      tailAbove p f ((2 : ℝ) ^ k) ≤ ε ∧
      p.variance f ≤ p.expect (fun x => f x ^ 2) := by
  refine ⟨clause52_truncation_error p f k, ?_⟩
  refine ⟨clause56_optimal_truncation p f k ε hf hm hbound, ?_⟩
  exact (_root_.Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic.StageBMONTECARLO.clause56_endpoint p f k ε hf hm hbound).2.2

/-- Replicating the stated layer ledger k times multiplies each nonzero resource count by k. -/
theorem clause56_stopping_ledger (k perLayer medianCount : ℕ) :
    (⟨1 + 2 * perLayer, 2 * perLayer, 2 * medianCount, 0⟩ : CostLedger).replicate k
      = ⟨k * (1 + 2 * perLayer), k * (2 * perLayer), k * (2 * medianCount), 0⟩ := by
  exact clause56_adaptive_stopping_ledger k perLayer medianCount

/-- A single repetition of the specified layer ledger uses 1 + 2 times `perLayer` copies. -/
theorem clause56_stopping_copies (perLayer : ℕ) :
    (CostLedger.replicate
        (⟨1 + 2 * perLayer, 2 * perLayer, 2 * perLayer, 0⟩ : CostLedger) 1).copies
      = 1 + 2 * perLayer := by
  simp [CostLedger.replicate]

/-- A positive pilot variance certificate yields a median failure bound and a
sufficient positive per-group sample budget. This local certification supports
the estimation framework of [Montanaro2015]. -/
theorem clause56_median_budget (p : FinDist X) (f : X → ℝ)
    (ω : DrawRecord n₀ X) (t ε : ℝ) (M : ℕ)
    (hε : 0 < ε) (hM : 0 < M)
    (hB : 0 < pilotVarianceBound f t ω)
    (hvar : p.variance f ≤ pilotVarianceBound f t ω) :
    (∑ ω' ∈ Finset.univ.filter (fun ω' : Fin M → Fin (certifiedSamplesPerGroup f t ε ω) → X =>
        ε < |p.medianOfMeans f ω' - p.expect f|),
        ∏ m, p.probOf (ω' m))
      ≤ 3 ^ (M / 2) / 2 ^ M ∧
      4 * p.variance f
        ≤ (certifiedSamplesPerGroup f t ε ω : ℝ) * ε ^ 2 ∧
      0 < certifiedSamplesPerGroup f t ε ω :=
  (clause56_endpoint_median_budget p f ω t ε M hε hM hB hvar)

/-- Unfolds the relative-estimation copy, reflection, classical sample, and schedule sample cost
formulas together with the stated parameter domain and 3/4 success arithmetic. -/
theorem clause57_endpoint (l : WalkLedger) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε)
    (hdom : ε < 27 * B / 4) :
    (theorem6Copies B ε = B + Real.log (1 / ε) * Real.log (Real.log (1 / ε))) ∧
      (theorem6Reflections B ε
        = (B / ε) * Real.log (B / ε) ^ 3 * Real.log (Real.log (B / ε))) ∧
      (classicalRelativeSamples B ε = B / ε ^ 2) ∧
      (theorem11Samples l B ε
        = (B * (l.schedule : ℝ) ^ 2 * Real.log (l.schedule : ℝ) / ε)
          * Real.log (B * l.schedule / ε) ^ 3
          * Real.log (Real.log (B * l.schedule / ε))) ∧
      (1 ≤ B ∧ 0 < ε ∧ ε < 27 * B / 4 ∧ 32 ≤ Nat.ceil (32 * B) ∧
        1 - ((1 : ℝ) / 4) = (3 : ℝ) / 4) := by
  refine ⟨rfl, rfl, rfl, rfl, clause57_theorem6_scope B ε hB hε hdom⟩

/-- Two table-selection outputs are at most k, and equal input results give equal outputs. -/
theorem clause58_table_select (k : ℕ) (m₁ m₂ : ℝ) :
    tableSelectProgram k m₁ ≤ k ∧ tableSelectProgram k m₂ ≤ k ∧
      (m₁ = m₂ → tableSelectProgram k m₁ = tableSelectProgram k m₂) := by
  refine ⟨clause58_selectedBand_le k m₁, clause58_selectedBand_le k m₂, ?_⟩
  intro h
  simp [tableSelectProgram, h]

/-- Combines the numerator sum bound and selected-band bound with the explicit classical bit,
table-selection, memory, persistent-space, and greatest-common-divisor gate formulas. -/
theorem clause58_endpoint (N k Q maxAbs : ℕ) (num : Fin N → ℤ)
    (hnum : ∀ i, 0 ≤ num i) (habs : ∀ i, num i ≤ maxAbs) :
    (∑ i, num i) ≤ (N : ℤ) * (maxAbs : ℤ) ∧
      classicalBitBudget N k Q maxAbs
        = Nat.log2 (N * maxAbs + 1) + Nat.log2 Q + Nat.log2 (k + 1) ∧
      ∀ m : ℝ, selectedBand k m ≤ k ∧
      tableSelectGates k = k ∧
      memoryBits N k Q maxAbs = Nat.log2 (N * maxAbs + 1) + k + 1 ∧
      persistentSpaceBits N k Q maxAbs = classicalBitBudget N k Q maxAbs ∧
      gcdGates (Nat.log2 (N * maxAbs + 1)) = Nat.log2 (N * maxAbs + 1) := by
  refine ⟨clause58_pilot_numerator_bound N Q maxAbs num hnum habs, rfl, ?_⟩
  intro m
  exact ⟨clause58_selectedBand_le k m, rfl, rfl, rfl, rfl⟩

end StageBMONTECARLO
end Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloRefined
