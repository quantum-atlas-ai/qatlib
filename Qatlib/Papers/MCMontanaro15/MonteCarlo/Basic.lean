/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloDefs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation
set_option warningAsError false
open Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SqEstimation.InnerProduct

set_option autoImplicit false

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic
namespace StageBMONTECARLO

open Qatlib
open Qatlib.Papers.MCMontanaro15.MonteCarlo.StageBMONTECARLO
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {X : Type} [Fintype X] [DecidableEq X]
variable {n₀ : ℕ}

theorem probEvent_mono {L : ℕ} (p : FinDist X) (E E' : (Fin L → X) → Prop)
    [DecidablePred E] [DecidablePred E'] (h : ∀ ω, E ω → E' ω) :
    p.probEvent E ≤ p.probEvent E' := by
  unfold FinDist.probEvent
  have hsub : Finset.filter E Finset.univ ⊆ Finset.filter E' Finset.univ := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨ha'.1, h a ha'.2⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ?_)
  unfold FinDist.probOf
  exact Finset.prod_nonneg fun k _ => p.nonneg _

theorem probEvent_of_mem_le {L : ℕ} (p : FinDist X) (E : (Fin L → X) → Prop)
    [DecidablePred E] (ω₀ : Fin L → X) (hω₀ : E ω₀) :
    p.probOf ω₀ ≤ p.probEvent E := by
  unfold FinDist.probEvent
  have hsub : ({ω₀} : Finset (Fin L → X)) ⊆ Finset.filter E Finset.univ := by
    intro a ha
    rw [Finset.mem_singleton] at ha
    subst ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω₀⟩
  have hle : (∑ x ∈ ({ω₀} : Finset (Fin L → X)), p.probOf x)
      ≤ ∑ x ∈ Finset.filter E Finset.univ, p.probOf x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by
      unfold FinDist.probOf
      exact Finset.prod_nonneg fun k _ => p.nonneg _)
  rw [Finset.sum_singleton] at hle
  exact hle

structure WalkLedger where

  schedule : ℕ

  reflections : ℕ

  relaxation : ℕ

  gamma : ℝ

  overlap : ℝ

theorem clause51_walk_state_error (l : WalkLedger) (hR : 0 < l.reflections) :
    (l.reflections : ℝ) * (l.gamma / l.reflections) + l.gamma = 2 * l.gamma := by
  field_simp
  ring

noncomputable def theorem11WalkSteps (l : WalkLedger) (ε δ : ℝ) : ℝ :=
  ((l.schedule : ℝ) ^ 2 * Real.sqrt (l.relaxation : ℝ) / ε)
    * Real.log (l.schedule / ε) ^ 5
    * Real.log (l.schedule / δ)
    * Real.log (Real.log (l.schedule / ε))

noncomputable def theorem11Reflections (l : WalkLedger) (ε : ℝ) : ℝ :=
  (l.schedule : ℝ) / ε * Real.log (l.schedule / ε) ^ 3
    * Real.log (Real.log (l.schedule / ε))

noncomputable def theorem11Copies (l : WalkLedger) (ε : ℝ) : ℝ :=
  Real.log (l.schedule / ε) * Real.log (Real.log (l.schedule / ε))

theorem clause51_endpoint_relative {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β ε : ℝ)
    (hβ : 0 ≤ β) (hε : 0 < ε)
    (hgap : (Fintype.card Ω : ℝ) * Real.exp (-β) ≤ ε * partitionFnLimit H) :
    (1 - ε) * partitionFnLimit H ≤ partitionFn H β ∧
      partitionFn H β ≤ (1 + ε) * partitionFnLimit H := by
  have hgap' := (partitionFn_sub_partitionFnLimit_le H β hβ)
  have hlim : partitionFnLimit H ≤ partitionFn H β := partitionFnLimit_le_partitionFn H β
  constructor
  · have hone : 1 - ε ≤ 1 := by linarith
    nlinarith
  · have hlow : 0 ≤ partitionFn H β - partitionFnLimit H := hgap'.1
    linarith

theorem clause51_endpoint {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (l : WalkLedger)
    (hR : 0 < l.reflections) (hg : 0 ≤ l.gamma) :
    partitionFnLimit H ≤ partitionFn H l.gamma ∧
      (l.reflections : ℝ) * (l.gamma / l.reflections) + l.gamma = 2 * l.gamma ∧
      0 ≤ partitionFn H l.gamma - partitionFnLimit H ∧
        partitionFn H l.gamma - partitionFnLimit H
          ≤ (Fintype.card Ω : ℝ) * Real.exp (-l.gamma) := by
  have hgap := partitionFn_sub_partitionFnLimit_le H l.gamma hg
  exact ⟨partitionFnLimit_le_partitionFn H l.gamma, clause51_walk_state_error l hR,
    hgap.1, hgap.2⟩

theorem clause52_layer_mean_shift (p q : FinDist X) (γ : ℝ) (w : X → ℝ)
    (hγ : tvDist p q ≤ γ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    |p.expect w - q.expect w| ≤ 2 * γ := by
  have h := expect_sub_tvDist p q w hw0 hw1
  calc
    |p.expect w - q.expect w| ≤ 2 * tvDist p q := h
    _ ≤ 2 * γ := by nlinarith [hγ]

theorem clause52_accumulated_layer_shift (k : ℕ) (γ : ℝ) :
    (∑ _i : Fin k, (2 * γ : ℝ)) = 2 * γ * (k : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

theorem clause52_error_ledger (p : FinDist X) (f : X → ℝ) (k : ℕ) (γ : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k) :
    tailAbove p f ((2 : ℝ) ^ k) + 2 * γ * (k : ℝ)
      ≤ p.expect (fun x => f x ^ 2) / (2 : ℝ) ^ k + 2 * γ * (k : ℝ) := by
  have h := tailAbove_le_secondMoment_div p f hf ((2 : ℝ) ^ k) hm
  linarith

theorem clause52_overlap_domain (B : ℝ) (hB : 1 ≤ B) : 0 < 1 / B ∧ 1 / B ≤ 1 := by
  constructor
  · exact one_div_pos.mpr (lt_of_lt_of_le (by norm_num) hB)
  · rw [div_le_iff₀ (by linarith : (0:ℝ) < B)]
    nlinarith

theorem clause52_endpoint (p : FinDist X) (f : X → ℝ) (k : ℕ) (γ : ℝ) (B : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k) (hB : 1 ≤ B) :
    (0 < 1 / B ∧ 1 / B ≤ 1) ∧
      tailAbove p f ((2 : ℝ) ^ k) + 2 * γ * (k : ℝ)
        ≤ p.expect (fun x => f x ^ 2) / (2 : ℝ) ^ k + 2 * γ * (k : ℝ) := by
  exact ⟨clause52_overlap_domain B hB, clause52_error_ledger p f k γ hf hm⟩

noncomputable def sourceLemma18Baseline (T : ℕ) (γ : ℝ) : ℝ :=
  3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ

theorem clause53_baseline_split (T : ℕ) (γ : ℝ) :
    sourceLemma18Baseline T γ
      = 3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ := rfl

theorem clause53_baseline_transport_is_union_bound (T : ℕ) (γ : ℝ) :
    (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ
      = ∑ _i : Fin T, (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

theorem clause53_sourceSuccessRate (T : ℕ) (γ : ℝ) :
    1 - sourceLemma18Baseline T γ
        = 7 / 10 - (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ ∧
      1 - ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) + (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ)
        = 2 / 3 - (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ := by
  constructor
  · unfold sourceLemma18Baseline
    ring
  · ring

noncomputable def sourceLemma18Transport (T : ℕ) (γ : ℝ) : ℝ :=
  (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ

theorem clause53_transport_union_bound (T : ℕ) (perRun : ℝ) :
    (T : ℝ) * perRun = ∑ _i : Fin T, perRun := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

theorem clause53_transport_ledger (T : ℕ) (γ : ℝ) :
    sourceLemma18Transport T γ = (T : ℝ) * (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ := by
  simp only [sourceLemma18Transport]
  ring

theorem clause53_intrinsic_failure_ledger (δ : ℝ) :
    (1 : ℝ) / 9 + 2 * δ = (1 : ℝ) / 9 + δ + δ := by ring

theorem clause53_sourcePrintedThreeTenths (δ : ℝ) :
    ((1 : ℝ) / 9 + 2 * δ ≤ 3 / 10 ↔ δ ≤ 17 / 180) ∧
      ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) = 1 / 3) ∧
      ((1 : ℝ) / 3 > 3 / 10) := by
  have h1 : ((1 : ℝ) / 9 + 2 * δ ≤ 3 / 10) ↔ (δ ≤ 17 / 180) := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have h2 : ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) = 1 / 3) := by norm_num
  have h3 : ((1 : ℝ) / 3 > 3 / 10) := by norm_num
  exact ⟨h1, h2, h3⟩

theorem clause53_transport_dyadic_mean_shift (p q : FinDist X) (γ : ℝ) (w : X → ℝ)
    (hγ : tvDist p q ≤ γ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    |p.expect w - q.expect w| ≤ 2 * γ :=
  clause52_layer_mean_shift p q γ w hγ hw0 hw1

theorem clause53_endpoint (δ : ℝ) (T : ℕ) (γ : ℝ) :
    ((1 : ℝ) / 9 + 2 * δ ≤ 3 / 10 ↔ δ ≤ 17 / 180) ∧
      sourceLemma18Transport T γ = (T : ℝ) * (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ ∧
      ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9) = 1 / 3) ∧
      ((1 : ℝ) / 3 > 3 / 10) ∧
      ((T : ℝ) * ((Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ)
        = ∑ _i : Fin T, (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ) ∧
      sourceLemma18Baseline T γ
        = 3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ ∧
      1 - sourceLemma18Baseline T γ
        = 7 / 10 - (Real.pi ^ 2 / Real.sqrt 6) * (T : ℝ) * Real.sqrt γ := by
  refine ⟨clause53_sourcePrintedThreeTenths δ |>.1, clause53_transport_ledger T γ,
    clause53_sourcePrintedThreeTenths δ |>.2.1, clause53_sourcePrintedThreeTenths δ |>.2.2,
    clause53_transport_union_bound T _, clause53_baseline_split T γ,
    (clause53_sourceSuccessRate T γ).1⟩

noncomputable def theorem5Copies (σ ε : ℝ) : ℝ :=
  Real.log (σ / ε) * Real.log (Real.log (σ / ε))

noncomputable def theorem5Reflections (σ ε : ℝ) : ℝ :=
  (σ / ε) * Real.log (σ / ε) ^ 3 * Real.log (Real.log (σ / ε))

theorem clause54_theorem5_accuracy_domain (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (hdom : ε < 4 * σ) :
    0 < ε / (32 * σ) ∧ ε / (32 * σ) < (1 : ℝ) / 8 ∧ (1 : ℝ) / 8 < (1 : ℝ) / 2 := by
  have hσpos : (0 : ℝ) < 32 * σ := by nlinarith
  constructor
  · exact div_pos hε hσpos
  · constructor
    · rw [div_lt_iff₀ hσpos]
      have hmul : (1 : ℝ) / 8 * (32 * σ) = 4 * σ := by ring
      rw [hmul]
      exact hdom
    · norm_num

theorem clause54_theorem5_success_rate :
    1 - ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9)) = 2 / 3 := by norm_num

def algorithm3Output (σ m muNeg muPos : ℝ) : ℝ := σ * (m - 4 * muNeg + 4 * muPos)

noncomputable def bandMeanBelow (p : FinDist X) (f : X → ℝ) (σ m : ℝ) : ℝ :=
  p.expect (fun i => -(bandBelowZero (centeredPayoff f σ m i)) / 4)

noncomputable def bandMeanAbove (p : FinDist X) (f : X → ℝ) (σ m : ℝ) : ℝ :=
  p.expect (fun i => (bandAtLeastZero (centeredPayoff f σ m i)) / 4)

theorem clause54_band_means (p : FinDist X) (f : X → ℝ) (σ m : ℝ) :
    p.expect (fun i => bandBelowZero (centeredPayoff f σ m i))
        = -4 * bandMeanBelow p f σ m ∧
      p.expect (fun i => bandAtLeastZero (centeredPayoff f σ m i))
        = 4 * bandMeanAbove p f σ m ∧
      p.expect (fun i => -(bandBelowZero (centeredPayoff f σ m i)))
        = 4 * bandMeanBelow p f σ m := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [bandMeanBelow, expect_div_const, expect_neg]
    ring
  · simp only [bandMeanAbove, expect_div_const]
    ring
  · simp only [bandMeanBelow, expect_div_const, expect_neg]
    ring

theorem clause54_algorithm3_error_ledger (p : FinDist X) (f : X → ℝ) (σ m muNeg muPos ε : ℝ)
    (hσ : 0 < σ)
    (hneg : |bandMeanBelow p f σ m - muNeg| ≤ ε)
    (hpos : |bandMeanAbove p f σ m - muPos| ≤ ε) :
    |algorithm3Output σ m muNeg muPos - p.expect (fun i => f i)| ≤ 8 * σ * ε := by
  have hrec := algorithm3_reconstruction p f σ m
  have hmeans := clause54_band_means p f σ m
  have hmid : |(m - 4 * muNeg + 4 * muPos) - p.expect (fun i => f i / σ)| ≤ 8 * ε := by
    have hrec' : p.expect (fun i => f i / σ)
        = m - 4 * bandMeanBelow p f σ m + 4 * bandMeanAbove p f σ m := by
      rw [← hrec, hmeans.2.2, hmeans.2.1]
    have hkey : (m - 4 * muNeg + 4 * muPos) - p.expect (fun i => f i / σ)
        = 4 * (bandMeanBelow p f σ m - muNeg) + 4 * (muPos - bandMeanAbove p f σ m) := by
      rw [hrec']
      ring
    rw [hkey]
    calc
      |4 * (bandMeanBelow p f σ m - muNeg) + 4 * (muPos - bandMeanAbove p f σ m)|
          ≤ |4 * (bandMeanBelow p f σ m - muNeg)|
            + |4 * (muPos - bandMeanAbove p f σ m)| := abs_add_le _ _
      _ = 4 * |bandMeanBelow p f σ m - muNeg|
            + 4 * |muPos - bandMeanAbove p f σ m| := by
          simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      _ ≤ 4 * ε + 4 * ε := by
        have h4neg := mul_le_mul_of_nonneg_left hneg (by norm_num : (0 : ℝ) ≤ 4)
        have h4pos := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 4)
        rw [abs_sub_comm] at h4pos
        exact add_le_add h4neg h4pos
      _ = 8 * ε := by ring
  have hid : p.expect (fun i => f i) = σ * p.expect (fun i => f i / σ) := by
    rw [expect_div_const]
    field_simp [ne_of_gt hσ]
  rw [algorithm3Output]
  rw [show σ * (m - 4 * muNeg + 4 * muPos) - p.expect (fun i => f i)
      = σ * ((m - 4 * muNeg + 4 * muPos) - p.expect (fun i => f i / σ)) by
        rw [hid]; ring]
  rw [abs_mul, abs_of_pos hσ]
  have hmul := mul_le_mul_of_nonneg_left hmid (le_of_lt hσ)
  nlinarith

theorem clause54_algorithm3_success (δ : ℝ) (hδ : δ ≤ (1 : ℝ) / 9) :
    1 - ((1 : ℝ) / 9 + 2 * δ) ≥ 2 / 3 ∧
      1 - ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9)) = 2 / 3 := by
  constructor <;> linarith

theorem clause54_endpoint (p : FinDist X) (f : X → ℝ) (σ m muNeg muPos ε : ℝ)
    (hσ : 0 < σ)
    (hneg : |bandMeanBelow p f σ m - muNeg| ≤ ε)
    (hpos : |bandMeanAbove p f σ m - muPos| ≤ ε) :
    |algorithm3Output σ m muNeg muPos - p.expect (fun i => f i)| ≤ 8 * σ * ε ∧
      1 - ((1 : ℝ) / 9 + 2 * ((1 : ℝ) / 9)) = 2 / 3 ∧
      (CostLedger.replicate
          { copies := 1 + 2 * 3
            reflections := 2 * 3
            medians := 2 * 3
            classicalBits := 0 } 1).copies = 7 ∧
      theorem5Copies σ ε = Real.log (σ / ε) * Real.log (Real.log (σ / ε)) ∧
      theorem5Reflections σ ε
        = (σ / ε) * Real.log (σ / ε) ^ 3 * Real.log (Real.log (σ / ε)) := by
  exact ⟨clause54_algorithm3_error_ledger p f σ m muNeg muPos ε hσ hneg hpos,
    (clause54_algorithm3_success (1 / 9) (by norm_num)).2, rfl, rfl, rfl⟩

theorem clause56_variance_le_one_of_bounded (p : FinDist X) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : p.variance f ≤ 1 := by
  rw [sq_real_variance_eq]
  have hsq : p.expect (fun x => f x ^ 2) ≤ 1 := by
    unfold FinDist.expect
    calc ∑ x, p.prob x * f x ^ 2
        ≤ ∑ x, p.prob x * 1 := by
          exact Finset.sum_le_sum fun x _ => by
            have h : f x ^ 2 ≤ 1 := by
              have := abs_le.mp (hf x)
              nlinarith [sq_nonneg (f x)]
            exact mul_le_mul_of_nonneg_left h (p.nonneg x)
      _ = 1 := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  have : 0 ≤ (p.expect f) ^ 2 := sq_nonneg _
  linarith

theorem clause56_variance_sq_le_one (p : FinDist X) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : p.variance (fun x => f x ^ 2) ≤ 1 := by
  have h : ∀ x, |f x ^ 2| ≤ 1 := by
    intro x
    have hab := abs_le.mp (hf x)
    have hs : f x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (f x - 1), sq_nonneg (f x + 1)]
    rw [abs_of_nonneg (sq_nonneg (f x))]
    exact hs
  exact clause56_variance_le_one_of_bounded p (fun x => f x ^ 2) h

theorem clause56_pilot_certificate (p : FinDist X) (f : X → ℝ) (hL : 0 < n₀)
    (hf : ∀ x, |f x| ≤ 1) (t : ℝ) (ht : 0 < t) :
    p.probEvent (L := n₀) (fun ω : DrawRecord n₀ X =>
      t < |pilotSecondMoment f ω - p.expect (fun x => f x ^ 2)|)
      ≤ 1 / (n₀ * t ^ 2) := by
  have h := p.chebyshev_avg (fun x => f x ^ 2) hL t ht
  have hsq : p.variance (fun x => f x ^ 2) ≤ 1 := clause56_variance_sq_le_one p f hf
  unfold pilotSecondMoment
  calc
    p.probEvent (L := n₀) (fun ω : DrawRecord n₀ X =>
        t < |FinDist.avg (fun x => f x ^ 2) ω - p.expect (fun x => f x ^ 2)|)
        ≤ p.variance (fun x => f x ^ 2) / ((n₀ : ℝ) * t ^ 2) := h
    _ ≤ 1 / ((n₀ : ℝ) * t ^ 2) := by
      exact div_le_div_of_nonneg_right hsq (by positivity)
    _ = 1 / (n₀ * t ^ 2) := by rfl

theorem clause56_pilot_certifies_variance (p : FinDist X) (f : X → ℝ)
    (ω : DrawRecord n₀ X) (t : ℝ) (hgood :
      |pilotSecondMoment f ω - p.expect (fun x => f x ^ 2)| ≤ t) :
    p.variance f ≤ pilotVarianceBound f t ω := by
  have hvar : p.variance f ≤ p.expect (fun x => f x ^ 2) := by
    rw [sq_real_variance_eq]
    have : 0 ≤ (p.expect f) ^ 2 := sq_nonneg _
    linarith
  have hsq : p.expect (fun x => f x ^ 2) ≤ pilotSecondMoment f ω + t := by
    have h := abs_le.mp hgood
    linarith [abs_nonneg (pilotSecondMoment f ω - p.expect (fun x => f x ^ 2))]
  unfold pilotVarianceBound
  linarith

theorem clause56_certified_stopping_is_record_only {n₀ : ℕ} (f : X → ℝ) (t ε : ℝ)
    (ω : DrawRecord n₀ X) :
    certifiedSamplesPerGroup f t ε ω
      = Nat.ceil (4 * (pilotSecondMoment f ω + t) / ε ^ 2) := by
  rfl

theorem clause56_certified_scale_meets_median_hypothesis (p : FinDist X) (f : X → ℝ)
    (ω : DrawRecord n₀ X) (t ε : ℝ) (hε : 0 < ε)
    (hB : 0 < pilotVarianceBound f t ω)
    (hvar : p.variance f ≤ pilotVarianceBound f t ω) :
    4 * p.variance f
        ≤ (certifiedSamplesPerGroup f t ε ω : ℝ) * ε ^ 2 ∧
      0 < certifiedSamplesPerGroup f t ε ω := by
  have hceil : 4 * pilotVarianceBound f t ω / ε ^ 2
      ≤ (certifiedSamplesPerGroup f t ε ω : ℝ) := by
    unfold certifiedSamplesPerGroup
    exact Nat.le_ceil _
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmul : (4 * pilotVarianceBound f t ω / ε ^ 2) * ε ^ 2
      = 4 * pilotVarianceBound f t ω := by
    field_simp [ne_of_gt hε2]
  constructor
  · have hstep : (4 * pilotVarianceBound f t ω / ε ^ 2) * ε ^ 2
        ≤ (certifiedSamplesPerGroup f t ε ω : ℝ) * ε ^ 2 :=
      mul_le_mul_of_nonneg_right hceil (le_of_lt hε2)
    rw [hmul] at hstep
    nlinarith [mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 4)]
  · unfold certifiedSamplesPerGroup
    have hpos : 0 < 4 * pilotVarianceBound f t ω / ε ^ 2 := by positivity
    exact Nat.ceil_pos.mpr hpos

theorem clause56_fresh_median_budget (p : FinDist X) (f : X → ℝ) (L M : ℕ) (ε : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hε : 0 < ε)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * ε ^ 2) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin M → Fin L → X =>
        ε < |p.medianOfMeans f ω - p.expect f|), ∏ m, p.probOf (ω m))
      ≤ 3 ^ (M / 2) / 2 ^ M := by
  exact p.median_of_means_concentration f hL hM ε hε hvar

theorem twoLevelLaw_allZero_prob {N : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (twoLevelLaw p hp0 hp1 N).probOf (fun _ : Fin n => (0 : Fin (N + 2))) = (1 - p) ^ n := by
  have hne : (0 : Fin (N + 2)) ≠ twoLevelLarge N := by
    intro h
    have hv : (0 : ℕ) = N + 1 := by
      simpa [twoLevelLarge] using! (congrArg Fin.val h)
    omega
  have h0 : (twoLevelLaw p hp0 hp1 N).prob (0 : Fin (N + 2)) = 1 - p := by
    simp [twoLevelLaw, hne]
  unfold FinDist.probOf
  have hprod : (∏ i : Fin n, (twoLevelLaw p hp0 hp1 N).prob ((fun _ => (0 : Fin (N + 2))) i))
      = ∏ _i : Fin n, (twoLevelLaw p hp0 hp1 N).prob (0 : Fin (N + 2)) :=
    Finset.prod_congr rfl (fun i _ => rfl)
  rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h0]

theorem twoLevelLaw_mean {N : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoLevelLaw p hp0 hp1 N).expect (fun x => (x : ℕ)) = p * (N + 1) := by
  have hne : (0 : Fin (N + 2)) ≠ twoLevelLarge N := by
    intro h
    have hv : (0 : ℕ) = N + 1 := by
      simpa [twoLevelLarge] using! (congrArg Fin.val h)
    omega
  have hval : (twoLevelLarge N : ℕ) = N + 1 := by
    simp [twoLevelLarge]
  have hmain : (∑ x : Fin (N + 2), (twoLevelLaw p hp0 hp1 N).prob x * (x : ℕ))
      = (1 - p) * ((0 : Fin (N + 2)) : ℕ) + p * ((twoLevelLarge N : Fin (N + 2)) : ℕ) := by
    have e : ∀ x, (twoLevelLaw p hp0 hp1 N).prob x * (x : ℕ)
        = (if x = 0 then (1 - p) * (x : ℕ) else 0)
          + (if x = twoLevelLarge N then p * (x : ℕ) else 0) := by
      intro x
      by_cases h0x : x = 0
      · by_cases h1x : x = twoLevelLarge N
        · simp only [twoLevelLaw, if_pos h0x, if_pos h1x]
          ring
        · simp only [twoLevelLaw, if_pos h0x, if_neg h1x]
          ring
      · by_cases h1x : x = twoLevelLarge N
        · simp only [twoLevelLaw, if_neg h0x, if_pos h1x]
          ring
        · simp only [twoLevelLaw, if_neg h0x, if_neg h1x]
          ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib]
    rw [Fintype.sum_ite_eq' (0 : Fin (N + 2)) (fun j => (1 - p) * (j : ℕ))]
    rw [Fintype.sum_ite_eq' (twoLevelLarge N) (fun j => p * (j : ℕ))]
  unfold FinDist.expect
  rw [hmain]
  simp [hval]

theorem clause55_no_go_two_level (alg : OpaqueSampler) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hdraw : (1 - p) ^ alg.draws > 1 / 3) :
    ∃ N : ℕ, 0 < N ∧
      (twoLevelLaw p (le_of_lt hp) hp1 N).probEvent
          (fun ω : Fin alg.draws → Fin (N + 2) =>
            1 / 4 < |alg.run (fun k => (ω k).val) - p * (N + 1)|) > 1 / 3 := by
  set y : ℝ := alg.run (fun _ => 0) with hy
  let M : ℕ := Nat.ceil ((|y| + 1 / 4) / p) + 1
  have hx : ((|y| + 1 / 4) / p) < (M : ℝ) := by
    have hceil := Nat.le_ceil ((|y| + 1 / 4) / p)
    have hlt : (Nat.ceil ((|y| + 1 / 4) / p) : ℝ)
        < (Nat.ceil ((|y| + 1 / 4) / p) : ℝ) + 1 := by
      exact_mod_cast (Nat.lt_succ_self (Nat.ceil ((|y| + 1 / 4) / p)))
    dsimp [M]
    rw [Nat.cast_succ]
    exact lt_of_le_of_lt hceil hlt
  have hnonneg : 0 ≤ (|y| + 1 / 4) / p := div_nonneg (by positivity) (le_of_lt hp)
  have hMone : (1 : ℕ) ≤ M := by
    dsimp [M]
    omega
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMone
  have hMnat : 0 < M := by exact_mod_cast hMpos
  have hpM0 : |y| + 1 / 4 < p * (M : ℝ) := by
    have := (div_lt_iff₀ hp).1 hx
    linarith
  have hpM : |y| + 1 / 4 < p * ((M : ℝ) + 1) := by
    have h2 : p * (M : ℝ) ≤ p * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hp)
    linarith [hpM0, h2]
  refine ⟨M, hMnat, ?_⟩
  have hsub : ∀ ω : Fin alg.draws → Fin (M + 2), (∀ k, ω k = 0) →
      1 / 4 < |alg.run (fun k => (ω k).val) - p * ((M : ℝ) + 1)| := by
    intro ω hω
    have hr : alg.run (fun k => (ω k).val) = y := by
      have hval : (fun k => (ω k).val) = (fun _ => (0 : ℕ)) := by
        funext k
        have hk := hω k
        simpa using! (congrArg Fin.val hk)
      rw [hval, hy]
    rw [hr]
    have hnonneg' : 0 ≤ p * ((M : ℝ) + 1) - y := by
      have hy' : y ≤ |y| := le_abs_self y
      linarith [hpM]
    rw [abs_sub_comm, abs_of_nonneg hnonneg']
    have hy' : y ≤ |y| := le_abs_self y
    linarith [hpM, hy']
  have hmono := probEvent_mono (twoLevelLaw p (le_of_lt hp) hp1 M)
    (fun ω : Fin alg.draws → Fin (M + 2) => ∀ k, ω k = 0)
    (fun ω : Fin alg.draws → Fin (M + 2) =>
      1 / 4 < |alg.run (fun k => (ω k).val) - p * ((M : ℝ) + 1)|) hsub
  have hle := probEvent_of_mem_le (twoLevelLaw p (le_of_lt hp) hp1 M)
    (fun ω : Fin alg.draws → Fin (M + 2) => ∀ k, ω k = 0)
    (fun _ => (0 : Fin (M + 2))) (by intro k; rfl)
  have hprob : (twoLevelLaw p (le_of_lt hp) hp1 M).probOf (fun _ => (0 : Fin (M + 2)))
      = (1 - p) ^ alg.draws :=
    twoLevelLaw_allZero_prob p (le_of_lt hp) hp1 alg.draws
  have hgt : (twoLevelLaw p (le_of_lt hp) hp1 M).probEvent
      (fun ω : Fin alg.draws → Fin (M + 2) =>
        1 / 4 < |alg.run (fun k => (ω k).val) - p * ((M : ℝ) + 1)|) > 1 / 3 := by
    linarith [hmono, hle, hprob, hdraw]
  exact hgt

theorem clause55_feasible_boundary (alg : OpaqueSampler) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hdraw : (1 - p) ^ alg.draws > 1 / 3) :
    ∃ N : ℕ, 0 < N ∧
      (twoLevelLaw p (le_of_lt hp) hp1 N).probEvent
          (fun ω : Fin alg.draws → Fin (N + 2) =>
            1 / 4 < |alg.run (fun k => (ω k).val) - p * (N + 1)|) > 1 / 3 :=
  clause55_no_go_two_level alg p hp hp1 hdraw

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
      law.variance f ≤ 1 := by
  refine ⟨clause55_no_go_two_level alg p hp hp1 hdraw,
    (clause53_sourcePrintedThreeTenths (1 / 9)).2.1,
    clause56_pilot_certifies_variance law f ω t hgood, rfl,
    clause56_pilot_certificate law f hn₀ hf t ht,
    clause56_variance_le_one_of_bounded law f hf⟩

theorem clause56_optimal_truncation (p : FinDist X) (f : X → ℝ) (k : ℕ) (ε : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k)
    (hbound : p.expect (fun x => f x ^ 2) ≤ (2 : ℝ) ^ k * ε) :
    tailAbove p f ((2 : ℝ) ^ k) ≤ ε := by
  have h := tailAbove_le_secondMoment_div p f hf ((2 : ℝ) ^ k) hm
  have h2 : p.expect (fun x => f x ^ 2) / (2 : ℝ) ^ k ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hbound]
  linarith

theorem clause56_adaptive_stopping_ledger (k perLayer medians : ℕ) :
    CostLedger.replicate
        ⟨1 + 2 * perLayer, 2 * perLayer, 2 * medians, 0⟩ k
      = ⟨k * (1 + 2 * perLayer), k * (2 * perLayer), k * (2 * medians), 0⟩ := by
  cases k <;> simp [CostLedger.replicate, mul_comm]

theorem clause56_endpoint (p : FinDist X) (f : X → ℝ) (k : ℕ) (ε : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < (2 : ℝ) ^ k)
    (hbound : p.expect (fun x => f x ^ 2) ≤ (2 : ℝ) ^ k * ε) :
    tailAbove p f ((2 : ℝ) ^ k) ≤ ε ∧
      CostLedger.replicate
          ⟨1 + 2 * k, 2 * k, 2 * k, 0⟩ 1
        = ⟨1 + 2 * k, 2 * k, 2 * k, 0⟩ ∧
      p.variance f ≤ p.expect (fun x => f x ^ 2) := by
  refine ⟨clause56_optimal_truncation p f k ε hf hm hbound,
    by simp [CostLedger.replicate], ?_⟩
  rw [sq_real_variance_eq]
  have : 0 ≤ (p.expect f) ^ 2 := sq_nonneg _
  linarith

theorem clause56_endpoint_median_budget (p : FinDist X) (f : X → ℝ)
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
      0 < certifiedSamplesPerGroup f t ε ω := by
  obtain ⟨hscale, hpos⟩ :=
    clause56_certified_scale_meets_median_hypothesis p f ω t ε hε hB hvar
  refine ⟨clause56_fresh_median_budget p f (certifiedSamplesPerGroup f t ε ω) M ε hpos hM hε hscale,
    hscale, hpos⟩

theorem clause57_theorem6_scope (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε)
    (hdom : ε < 27 * B / 4) :
    1 ≤ B ∧ 0 < ε ∧ ε < 27 * B / 4 ∧ 32 ≤ Nat.ceil (32 * B) ∧
      1 - ((1 : ℝ) / 4) = (3 : ℝ) / 4 := by
  have hBpos : (0 : ℝ) < B := by linarith
  have h32 : (32 : ℝ) * B ≤ (Nat.ceil (32 * B) : ℝ) := Nat.le_ceil _
  have h32b : (32 : ℝ) ≤ 32 * B := by nlinarith
  refine ⟨hB, hε, hdom, ?_, by norm_num⟩
  have : (32 : ℝ) ≤ (Nat.ceil (32 * B) : ℝ) := le_trans h32b h32
  exact_mod_cast this

noncomputable def theorem6Copies (B ε : ℝ) : ℝ :=
  B + Real.log (1 / ε) * Real.log (Real.log (1 / ε))

noncomputable def theorem6Reflections (B ε : ℝ) : ℝ :=
  (B / ε) * Real.log (B / ε) ^ 3 * Real.log (Real.log (B / ε))

noncomputable def theorem11Samples (l : WalkLedger) (B ε : ℝ) : ℝ :=
  (B * (l.schedule : ℝ) ^ 2 * Real.log (l.schedule : ℝ) / ε)
    * Real.log (B * l.schedule / ε) ^ 3
    * Real.log (Real.log (B * l.schedule / ε))

noncomputable def classicalRelativeSamples (B ε : ℝ) : ℝ := B / ε ^ 2

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

noncomputable def selectedBand (k : ℕ) (m : ℝ) : ℕ :=
  if m < 0 then 0 else min k (Nat.floor (Real.log (max 1 |m|)))

theorem clause58_selectedBand_le (k : ℕ) (m : ℝ) : selectedBand k m ≤ k := by
  unfold selectedBand
  split
  · omega
  · exact min_le_left _ _

theorem clause58_select_result_dependent (k : ℕ) (m₁ m₂ : ℝ)
    (h : selectedBand k m₁ ≠ selectedBand k m₂) : m₁ ≠ m₂ := by
  intro hEq
  subst hEq
  exact absurd rfl h

theorem clause58_pilot_numerator_bound (N _Q maxAbs : ℕ) (num : Fin N → ℤ)
    (hnum : ∀ i, 0 ≤ num i) (habs : ∀ i, num i ≤ maxAbs) :
    (∑ i, num i) ≤ (N : ℤ) * (maxAbs : ℤ) := by
  calc
    (∑ i, num i) = ∑ i, |num i| := by
      exact Finset.sum_congr rfl (fun i _ => (abs_of_nonneg (hnum i)).symm)
    _ ≤ ∑ _i : Fin N, (maxAbs : ℤ) := Finset.sum_le_sum fun i _ => by
      rw [abs_of_nonneg (hnum i)]
      exact_mod_cast habs i
    _ = (N : ℤ) * (maxAbs : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp

def classicalBitBudget (N k Q maxAbs : ℕ) : ℕ :=
  Nat.log2 (N * maxAbs + 1) + Nat.log2 Q + Nat.log2 (k + 1)

theorem clause58_endpoint (N k Q maxAbs : ℕ) (num : Fin N → ℤ)
    (hnum : ∀ i, 0 ≤ num i) (habs : ∀ i, num i ≤ maxAbs) :
    (∑ i, num i) ≤ (N : ℤ) * (maxAbs : ℤ) ∧
      classicalBitBudget N k Q maxAbs
        = Nat.log2 (N * maxAbs + 1) + Nat.log2 Q + Nat.log2 (k + 1) ∧
      ∀ m : ℝ, selectedBand k m ≤ k := by
  exact ⟨clause58_pilot_numerator_bound N Q maxAbs num hnum habs, rfl,
    fun m => clause58_selectedBand_le k m⟩

end StageBMONTECARLO
end Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic
