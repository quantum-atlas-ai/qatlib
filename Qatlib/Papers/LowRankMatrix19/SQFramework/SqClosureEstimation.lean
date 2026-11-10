/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowRankMatrix19.SQFramework.SqClosureEstimationDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CacheOp
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS.SqBitLedger
open Qatlib.Papers.LowRankMatrix19.SQFramework.ConstructionStageB.StageBSQCLOSUREESTIMATION
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.LowRankMatrix19.SQFramework
namespace ConstructionStageB
namespace StageBSQCLOSUREESTIMATION

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius

noncomputable section

theorem sqPilotEnergy_eq {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ)
    (p : FinDist K) (r : ℕ) (ω : Fin r → K) :
    sqPilotEnergy A p r ω = FinDist.avg (fun k => sketchRowSquared A k / p.prob k) ω := by
  exact compactSketched_energy_avg p r ω A

theorem sqPilotEnergy_unbiased {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ)
    (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r) :
    (∑ ω : Fin r → K, (energySamplingLaw A hA).probOf ω
        * sqPilotEnergy A (energySamplingLaw A hA) r ω) = sketchSquared A := by
  have h1 : ∀ ω : Fin r → K, sqPilotEnergy A (energySamplingLaw A hA) r ω
      = FinDist.avg (fun k => sketchRowSquared A k / (energySamplingLaw A hA).prob k) ω := by
    intro ω
    exact sqPilotEnergy_eq A (energySamplingLaw A hA) r ω
  have h2 := (energySamplingLaw A hA).expect_avg
      (fun k => sketchRowSquared A k / (energySamplingLaw A hA).prob k) (L := r) hr
  calc (∑ ω : Fin r → K, (energySamplingLaw A hA).probOf ω
        * sqPilotEnergy A (energySamplingLaw A hA) r ω)
      = (∑ ω : Fin r → K, (energySamplingLaw A hA).probOf ω
        * FinDist.avg (fun k => sketchRowSquared A k / (energySamplingLaw A hA).prob k) ω) := by
        exact Finset.sum_congr rfl (fun ω _ => by rw [h1 ω])
      _ = (energySamplingLaw A hA).expect
          (fun k => sketchRowSquared A k / (energySamplingLaw A hA).prob k) := h2
      _ = sketchSquared A :=
        sketch_energy_expectation (energySamplingLaw A hA) A 1 (by norm_num) hA
          (energySampling_dominates_one A hA)

theorem sqPilotConcentration {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (energySamplingLaw A hA).probEvent (fun ω : Fin r → K =>
      sqPilotScale 1 δ r * sketchSquared A
        ≤ |sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A|) ≤ δ := by
  have h := (compact_sketch_frobenius_norm_bounds_and_tail K C (energySamplingLaw A hA) r A 1
    hr (by norm_num) hA (energySampling_dominates_one A hA)).2.2.2 δ hδ hδ1
  simpa [sqPilotScale, sqPilotEnergy, sqRowSketch] using! h

theorem sqPilotOverEstimate {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ)
    (hA : 0 < sketchSquared A) (r : ℕ) (δ : ℝ) (ω : Fin r → K)
    (hgood : |sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A|
      < sqPilotScale 1 δ r * sketchSquared A)
    (hc : sqPilotScale 1 δ r < 1) :
    sketchSquared A < sqPilotUpperEstimate (sqPilotEnergy A (energySamplingLaw A hA) r ω)
      (sqPilotScale 1 δ r) := by
  have h1 : (1 - sqPilotScale 1 δ r) * sketchSquared A
      < sqPilotEnergy A (energySamplingLaw A hA) r ω := by
    have habs : sketchSquared A - sqPilotEnergy A (energySamplingLaw A hA) r ω
        ≤ |sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A| := by
      have := neg_le_abs (sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A)
      linarith
    linarith
  have h2 : 0 < 1 - sqPilotScale 1 δ r := by linarith
  have h1' : sketchSquared A * (1 - sqPilotScale 1 δ r)
      < sqPilotEnergy A (energySamplingLaw A hA) r ω := by linarith
  unfold sqPilotUpperEstimate
  exact (lt_div_iff₀ h2).2 h1'

theorem sqPilotSampleCount_eq (ehat cdev L ε φ δ : ℝ) (rank : ℕ) :
    sqPilotSampleCount ehat cdev L ε φ δ rank
      = 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
        * (ehat / (1 - cdev)) ^ 2 / ε ^ 2 := rfl

theorem sqPilotBudget {L ε φ δ E ehat cdev : ℝ} {rank r : ℕ} (hL : 0 < L) (hε : 0 < ε)
    (hφ : 1 ≤ φ) (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 0 < E) (hr : 0 < r) (hehat : 0 < ehat)
    (hcdev1 : cdev < 1)
    (hcount : sqPilotSampleCount ehat cdev L ε φ δ rank ≤ (r : ℝ))
    (hover : sqPilotUpperEstimate ehat cdev ≥ E) :
    L * rankLogFactor rank * rowTailScale φ δ r E ≤ ε / 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsq : (ehat / (1 - cdev)) ^ 2 ≥ E ^ 2 := by
    have hover' : ehat / (1 - cdev) ≥ E := by
      simpa [sqPilotUpperEstimate] using! hover
    have hpos : 0 ≤ ehat / (1 - cdev) := by
      apply div_nonneg hehat.le
      linarith
    have hEpos : 0 ≤ E := hE.le
    have hdiff : 0 ≤ ehat / (1 - cdev) - E := by linarith [hover']
    have h1 : E * E ≤ (ehat / (1 - cdev)) * E := mul_le_mul_of_nonneg_right hover' hEpos
    have h2 : (ehat / (1 - cdev)) * E ≤ (ehat / (1 - cdev)) * (ehat / (1 - cdev)) :=
      mul_le_mul_of_nonneg_left hover' hpos
    have h3 : E * E ≤ (ehat / (1 - cdev)) * (ehat / (1 - cdev)) := h1.trans h2
    simpa [pow_two] using! h3
  have hX : 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2
      ≤ 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
        * (ehat / (1 - cdev)) ^ 2 := by
    have hlog : 0 ≤ Real.log (2 / (δ / 3)) :=
      le_of_lt (log_two_over_delta_third_pos hδ hδ1)
    have hφ2 : 0 ≤ φ ^ 2 := sq_nonneg _
    have hL2 : 0 ≤ (L * rankLogFactor rank) ^ 2 := sq_nonneg _
    have hcoeff : 0 ≤ 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hφ2) hlog) hL2
    exact mul_le_mul_of_nonneg_left hsq hcoeff
  have hcount' : 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
      * (ehat / (1 - cdev)) ^ 2 ≤ (r : ℝ) * ε ^ 2 := by
    have h := hcount
    rw [sqPilotSampleCount_eq] at h
    have := (div_le_iff₀ hε2).mp h
    exact this
  have hbudget : rowBudgetMul L ε φ δ E rank r := by
    unfold rowBudgetMul
    calc 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2
        ≤ 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
            * (ehat / (1 - cdev)) ^ 2 := hX
      _ ≤ (r : ℝ) * ε ^ 2 := hcount'
      _ = ε ^ 2 * (r : ℝ) := by ring
  exact rowTailBudget hL hε hφ hδ hδ1 hE.le hr hbudget

theorem aliasLaw_prob {n : ℕ} (w : Fin n → ℕ) (W : ℕ) (hW : 0 < W) (h : aliasTotal w = W)
    (i : Fin n) : (aliasLaw w W hW h).prob i = (w i : ℝ) / W := rfl

theorem aliasLaw_sum_one {n : ℕ} (w : Fin n → ℕ) (W : ℕ) (hW : 0 < W) (h : aliasTotal w = W) :
    (∑ i, (aliasLaw w W hW h).prob i) = 1 :=
  (aliasLaw w W hW h).sum_one

theorem alias_preprocess_cost (n : ℕ) : aliasPreprocessCost n = 2 * n + 1 := rfl

theorem alias_preprocess_cost_le (n : ℕ) (hn : 1 ≤ n) : aliasPreprocessCost n ≤ 3 * n := by
  unfold aliasPreprocessCost
  omega

theorem alias_space_cost (n : ℕ) : aliasSpaceCost n = n := rfl

theorem alias_draw_cost : aliasDrawCost = 1 := rfl

theorem alias_total_cost (n q : ℕ) : aliasTotalCost n q = aliasPreprocessCost n + q := by
  simp [aliasTotalCost, aliasDrawCost]

theorem alias_preprocess_not_dominant (n q : ℕ) :
    (aliasPreprocessCost n ≤ q * aliasDrawCost) ↔ (2 * n + 1 ≤ q) := by
  unfold aliasPreprocessCost aliasDrawCost
  omega

theorem alias_preprocess_le_total (n q : ℕ) :
    aliasPreprocessCost n ≤ aliasTotalCost n q := by
  unfold aliasTotalCost
  omega

theorem sqClosureLedger_eq (n r c q : ℕ) :
    sqClosureLedger n r c q = sketchArithmeticLedger n r c q := rfl

theorem sqClosure_fairBits_eq (draws : ℕ) : sqClosureFairBits draws = draws := rfl

theorem sqClosure_bitTime_ge_ram (n r c q : ℕ) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < (sqClosureLedger n r c q).reads + (sqClosureLedger n r c q).multiplies) :
    (sqClosureLedger n r c q).ramOps < (sqClosureLedger n r c q).bitTime w :=
  SqBitLedger.bitTime_gt_ramOps _ w hw hpos

theorem sqPilotMoments_cast {I : Type} [Fintype I] [DecidableEq I] (N : ℕ)
    (f : I → ℚ) (omega : Fin N → I) :
    ((pilotMoments N f omega).1 : ℝ) = FinDist.avg (fun i => (f i : ℝ)) omega ∧
      ((pilotMoments N f omega).2.1 : ℝ) = FinDist.avg (fun i => (f i : ℝ) ^ 2) omega :=
  pilotMoments_cast_avg N f omega

theorem sqClosure_fixedRound_error {x : ℝ} (p : ℕ) :
    |fixedRound p x - x| ≤ (pow2 p)⁻¹ := by
  have hpow : 0 < pow2 p := by unfold pow2; positivity
  have hne : pow2 p ≠ 0 := ne_of_gt hpow
  have hfloor : ((Int.floor (x * pow2 p) : ℤ) : ℝ) ≤ x * pow2 p := Int.floor_le (x * pow2 p)
  have hfloor' : (x * pow2 p - 1 : ℝ) < ((Int.floor (x * pow2 p) : ℤ) : ℝ) := by
    have hlt := Int.lt_floor_add_one (x * pow2 p)
    linarith
  have h1 : |(((Int.floor (x * pow2 p) : ℤ) : ℝ) - x * pow2 p)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold fixedRound
  have heq : ((Int.floor (x * pow2 p) : ℤ) : ℝ) / pow2 p - x
      = (((Int.floor (x * pow2 p) : ℤ) : ℝ) - x * pow2 p) / pow2 p := by
    field_simp [hne]
  rw [heq, abs_div, abs_of_pos hpow]
  have h2 : |(((Int.floor (x * pow2 p) : ℤ) : ℝ) - x * pow2 p)| / pow2 p ≤ 1 / pow2 p :=
    (div_le_div_iff_of_pos_right hpow).2 h1
  have hone : 1 / pow2 p = (pow2 p)⁻¹ := by
    rw [one_div]
  rw [hone] at h2
  exact h2

theorem sqPilotStrategy_good {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (energySamplingLaw A hA).probEvent (fun ω : Fin r → K =>
      sqPilotScale 1 (δ / 3) r * sketchSquared A
        ≤ |sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A|) ≤ δ / 3 ∧
      δ / 3 + δ / 3 ≤ δ := by
  refine ⟨?_, ?_⟩
  · exact sqPilotConcentration A hA r hr (δ / 3) (by linarith) (by linarith)
  · linarith

theorem clause18_endpoint {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∑ ω : Fin r → K, (energySamplingLaw A hA).probOf ω
        * sqPilotEnergy A (energySamplingLaw A hA) r ω) = sketchSquared A ∧
      (energySamplingLaw A hA).probEvent (fun ω : Fin r → K =>
        sqPilotScale 1 (δ / 3) r * sketchSquared A
          ≤ |sqPilotEnergy A (energySamplingLaw A hA) r ω - sketchSquared A|) ≤ δ / 3 ∧
      δ / 3 + δ / 3 ≤ δ := by
  exact ⟨sqPilotEnergy_unbiased A hA r hr, sqPilotStrategy_good A hA r hr δ hδ hδ1⟩

theorem clause19_endpoint {n : ℕ} (w : Fin n → ℕ) (W : ℕ) (hW : 0 < W)
    (h : aliasTotal w = W) (q : ℕ) :
    (∑ i, (aliasLaw w W hW h).prob i) = 1 ∧
      aliasPreprocessCost n = 2 * n + 1 ∧
      aliasSpaceCost n = n ∧
      aliasTotalCost n q = aliasPreprocessCost n + q ∧
      ((aliasPreprocessCost n ≤ q * aliasDrawCost) ↔ (2 * n + 1 ≤ q)) := by
  refine And.intro (aliasLaw_sum_one w W hW h) ?_
  refine And.intro (alias_preprocess_cost n) ?_
  refine And.intro (alias_space_cost n) ?_
  refine And.intro (alias_total_cost n q) ?_
  exact alias_preprocess_not_dominant n q

theorem clause20_endpoint (n r c q : ℕ) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < (sqClosureLedger n r c q).reads + (sqClosureLedger n r c q).multiplies)
    (draws : ℕ) (x : ℝ) (p : ℕ) :
    sqClosureLedger n r c q = sketchArithmeticLedger n r c q ∧
      (sqClosureLedger n r c q).ramOps < (sqClosureLedger n r c q).bitTime w ∧
      sqClosureFairBits draws = draws ∧
      |fixedRound p x - x| ≤ (pow2 p)⁻¹ := by
  exact ⟨sqClosureLedger_eq n r c q, sqClosure_bitTime_ge_ram n r c q w hw hpos,
    sqClosure_fairBits_eq draws, sqClosure_fixedRound_error p⟩

end

end StageBSQCLOSUREESTIMATION
