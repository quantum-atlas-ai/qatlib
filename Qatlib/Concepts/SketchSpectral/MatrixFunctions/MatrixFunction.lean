/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.MatrixFunctionDefs
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.EvenSVT
open Qatlib.Concepts.SketchSpectral.SketchAnalysis
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.ConstructionStageB.StageBSQMATRIXFUNCTION
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.ConstructionStageB.StageBSQMATRIXFUNCTION.Lemma49Ledger

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
namespace ConstructionStageB
namespace StageBSQMATRIXFUNCTION

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem g23_lemma49_rate_φ_mono (φ₁ φ₂ ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hφ₁ : 0 ≤ φ₁) (hφ₂ : φ₁ ≤ φ₂) :
    lemma49SampleRate φ₁ ε δ ≤ lemma49SampleRate φ₂ ε δ := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; simpa using! hδ1.le)
  have hsq : φ₁ ^ 2 ≤ φ₂ ^ 2 := (sq_le_sq₀ hφ₁ (le_trans hφ₁ hφ₂)).mpr hφ₂
  unfold lemma49SampleRate
  rw [div_le_div_iff₀ (sq_pos_of_pos hε) (sq_pos_of_pos hε)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hlog) (sq_nonneg ε)

theorem g23_lemma49_rate_ε_mono (φ ε₁ ε₂ δ : ℝ)
    (hε₁ : 0 < ε₁) (hε₂ : ε₁ ≤ ε₂) (hδ : 0 < δ) (hδ1 : δ < 1) :
    lemma49SampleRate φ ε₂ δ ≤ lemma49SampleRate φ ε₁ δ := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; simpa using! hδ1.le)
  have hε₂pos : 0 < ε₂ := lt_of_lt_of_le hε₁ hε₂
  have hsq : ε₁ ^ 2 ≤ ε₂ ^ 2 := (sq_le_sq₀ hε₁.le (le_trans hε₁.le hε₂)).mpr hε₂
  unfold lemma49SampleRate
  rw [div_le_div_iff₀ (sq_pos_of_pos hε₂pos) (sq_pos_of_pos hε₁)]
  exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg φ) hlog)

theorem g23_lemma49_rate_δ_mono (φ ε δ₁ δ₂ : ℝ)
    (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hδ₂ : δ₁ ≤ δ₂) :
    lemma49SampleRate φ ε δ₂ ≤ lemma49SampleRate φ ε δ₁ := by
  have hdiv : 1 / δ₂ ≤ 1 / δ₁ := one_div_le_one_div_of_le hδ₁ hδ₂
  have hlog : Real.log (1 / δ₂) ≤ Real.log (1 / δ₁) :=
    Real.log_le_log (div_pos (by linarith) (by linarith)) hdiv
  unfold lemma49SampleRate
  rw [div_le_div_iff₀ (sq_pos_of_pos hε) (sq_pos_of_pos hε)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (sq_nonneg φ)) (sq_nonneg ε)

theorem clause23_lemma49_total_is_two_row (φ ε δ : ℝ) :
    lemma49TotalSamples φ ε δ = 2 * lemma49RowSamples φ ε δ := by
  unfold lemma49TotalSamples lemma49RowSamples lemma49ColSamples lemma49SampleRate
  ring

theorem clause23_lemma49_budget_iff (φ ε δ : ℝ) (hε : 0 < ε) (r : ℕ) :
    lemma49SampleBudgetMul φ ε δ r ↔ lemma49RowSamples φ ε δ ≤ r := by
  have hne : ε ^ 2 ≠ 0 := by rw [pow_two]; exact mul_ne_zero (ne_of_gt hε) (ne_of_gt hε)
  unfold lemma49SampleBudgetMul lemma49RowSamples lemma49SampleRate
  constructor
  · intro h
    rw [div_le_iff₀ (sq_pos_of_pos hε)]
    exact h.trans (le_of_eq (mul_comm _ _))
  · intro h
    calc φ ^ 2 * Real.log (1 / δ) = (φ ^ 2 * Real.log (1 / δ) / ε ^ 2) * ε ^ 2 :=
        (div_mul_cancel₀ _ hne).symm
      _ ≤ r * ε ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg ε)
      _ = ε ^ 2 * r := by ring

theorem clause23_lemma49_sketch_time_shape (r c perSample : ℕ) :
    lemma49SketchTime r c perSample = (r + c) * perSample := rfl

theorem clause23_lemma49_ledger_covers_reads (l : Lemma49Ledger) (hper : 1 ≤ l.perSample) :
    l.samplerReads ≤ l.runtime ∧ l.probReads ≤ l.runtime := by
  have hsum : l.rowSamples + l.colSamples ≤ (l.rowSamples + l.colSamples) * l.perSample := by
    have h := Nat.mul_le_mul_left (l.rowSamples + l.colSamples) hper
    simpa using! h
  exact ⟨hsum, hsum⟩

theorem clause23_lemma49_ledger_runtime (l : Lemma49Ledger) :
    l.runtime = lemma49SketchTime l.rowSamples l.colSamples l.perSample := rfl

theorem clause23_lemma414_cutoff_budget (η₁ η₂ : ℝ) :
    lemma414CutoffBudget η₁ η₂ = 2 * η₁ + 2 * η₂ := rfl

theorem clause23_lemma414_cutoff_sq (σk η₁ η₂ : ℝ)
    (hcut : lemma414CutoffBudget η₁ η₂ ≤ σk ^ 2) :
    lemma414Cutoff σk η₁ η₂ ^ 2 = σk ^ 2 - lemma414CutoffBudget η₁ η₂ := by
  have hnonneg : 0 ≤ σk ^ 2 - lemma414CutoffBudget η₁ η₂ := by linarith
  unfold lemma414Cutoff
  exact Real.sq_sqrt hnonneg

theorem clause23_lemma414_isometry_budget_iff (η₂ α τ : ℝ) (hα : 0 < α) :
    lemma414IsometryBudget η₂ α ≤ τ ^ 2 ↔ η₂ ≤ τ ^ 2 * α := by
  unfold lemma414IsometryBudget
  exact div_le_iff₀ hα

theorem clause23_lemma414_col_over_row (φ normA normAF σk α δ : ℝ)
    (hσ : 0 < σk) (hα : α ≠ 0) :
    lemma414ColSamples φ normA normAF σk α δ
      = lemma414RowSamples φ normA normAF σk δ * (1 / α ^ 2) := by
  have hα2 : α ^ 2 ≠ 0 := by rw [pow_two]; exact mul_ne_zero hα hα
  have hσ2 : σk ^ 2 ≠ 0 := by rw [pow_two]; exact mul_ne_zero (ne_of_gt hσ) (ne_of_gt hσ)
  have hσ4 : σk ^ 4 ≠ 0 := by
    have h : σk ^ 4 = σk ^ 2 * σk ^ 2 := by ring
    rw [h]
    exact mul_ne_zero hσ2 hσ2
  have hprod : σk ^ 4 * α ^ 2 ≠ 0 := mul_ne_zero hσ4 hα2
  unfold lemma414ColSamples lemma414RowSamples
  field_simp [hα2, hσ2, hσ4, hprod]

theorem clause23_lemma414_frozen_retention {K C RS CT : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (k : ℕ) (η₁ η₂ τ : ℝ)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hkRS : k ≤ Fintype.card RS) (hkC : k ≤ Fintype.card C)
    (hσ : 0 < matrixSingularValues A k)
    (h1 : spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ η₁)
    (h2 : spectralFrobenius (Cc * Ccᴴ - R * Rᴴ) ≤ η₂)
    (hcut : τ * τ + lemma414CutoffBudget η₁ η₂ ≤ (matrixSingularValues A k) ^ 2) :
    ∀ i : ℕ, i < k → τ ≤ matrixSingularValues Cc i := by
  refine Qatlib.Concepts.SketchSpectral.EvenSVT.thresholdRankRetention
    K C RS CT A R Cc k η₁ η₂ τ hη₁ hη₂ hkRS hkC hσ h1 h2 ?_
  have hkey : τ * τ + 2 * η₁ + 2 * η₂ = τ * τ + lemma414CutoffBudget η₁ η₂ := by
    unfold lemma414CutoffBudget
    ring
  rw [hkey]
  exact hcut

theorem clause23_lemma414_frozen_second_isometry {C RS CT : Type} [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (τ α η₂ : ℝ)
    (hτ : 0 < τ) (hα : 0 ≤ α) (hη₂ : 0 ≤ η₂)
    (h2 : spectralFrobenius (Cc * Ccᴴ - R * Rᴴ) ≤ η₂)
    (hbudget : η₂ ≤ τ * τ * α) :
    ‖lemma414SecondIsometryResidual R Cc τ‖ ≤ α := by
  have h := Qatlib.Concepts.SketchSpectral.EvenSVT.truncatedSketchSecondIsometry
    C RS CT R Cc τ α η₂ hτ hα hη₂ h2 hbudget
  simpa only [lemma414SecondIsometryResidual] using! h

theorem clause23_first_gram_bad_mass_eq_frozen {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (η : ℝ) :
    firstGramBadMass p r A η = Qatlib.Concepts.SketchSpectral.SketchAnalysis.compactGramOperatorBadMass p r A η := rfl

theorem clause23_first_gram_tail_scale_le (φ δ : ℝ) (r : ℕ) (E ε : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 4) (hr : 0 < r) (hE : 0 ≤ E) (hε : 0 < ε)
    (hbudget : 8 * φ ^ 2 * Real.log (2 / (δ / 2)) ≤ ε ^ 2 * (r : ℝ)) :
    firstGramTailScale φ δ r E ≤ ε * E := by
  have hlog : 0 ≤ Real.log (2 / (δ / 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : 0 < (δ / 2 : ℝ))]
    linarith
  have hinner : 8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (r : ℝ) ≤ ε ^ 2 := by
    rw [div_le_iff₀ (by exact_mod_cast hr)]
    linarith
  have hsqrt : Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (r : ℝ)) ≤ ε := by
    have hsq : Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (r : ℝ))
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hinner
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hε] at hsq
  unfold firstGramTailScale
  exact mul_le_mul_of_nonneg_right hsqrt hE

theorem clause23_lemma55_operator_range (a b : ℝ) :
    lemma55OperatorRange a b = b - a := rfl

theorem clause23_lemma55_log_factor_ge_one (a b diff : ℝ)
    (hab : a ≤ b) (hdiff : 0 < diff) (hdiffle : diff ≤ b - a) :
    1 ≤ lemma55LogFactor a b diff := by
  have habne : a ≠ b := by
    intro hcon
    have hzero : b - a = 0 := by linarith
    linarith
  have hablt : a < b := lt_of_le_of_ne hab habne
  have hrange : 0 < lemma55OperatorRange a b := by
    unfold lemma55OperatorRange
    linarith
  have hx : 1 ≤ lemma55OperatorRange a b / diff := by
    rw [le_div_iff₀ hdiff]
    unfold lemma55OperatorRange
    linarith
  have hlog : 0 ≤ Real.log (lemma55OperatorRange a b / diff) := Real.log_nonneg hx
  have hfac : lemma55LogFactor a b diff = 1 + Real.log (lemma55OperatorRange a b / diff) := by
    unfold lemma55LogFactor
    rw [Real.log_mul (Real.exp_ne_zero 1)
      (div_ne_zero (ne_of_gt hrange) (ne_of_gt hdiff)),
      Real.log_exp]
  linarith

theorem clause23_lemma55_log_factor_mono (a b₁ b₂ diff : ℝ)
    (ha₁ : a < b₁) (hdiff : 0 < diff) (hb : b₁ ≤ b₂) :
    lemma55LogFactor a b₁ diff ≤ lemma55LogFactor a b₂ diff := by
  have hrange1 : 0 < lemma55OperatorRange a b₁ := by
    unfold lemma55OperatorRange
    linarith
  have hrange2 : 0 < lemma55OperatorRange a b₂ := by
    unfold lemma55OperatorRange
    linarith
  have hmul : b₁ * diff ≤ b₂ * diff := mul_le_mul_of_nonneg_right hb hdiff.le
  have hx : lemma55OperatorRange a b₁ / diff ≤ lemma55OperatorRange a b₂ / diff := by
    rw [div_le_div_iff₀ hdiff hdiff]
    unfold lemma55OperatorRange
    nlinarith [hmul]
  have hlog : Real.log (lemma55OperatorRange a b₁ / diff)
      ≤ Real.log (lemma55OperatorRange a b₂ / diff) :=
    Real.log_le_log (div_pos hrange1 hdiff) hx
  unfold lemma55LogFactor
  rw [Real.log_mul (Real.exp_ne_zero 1)
    (div_ne_zero (ne_of_gt hrange1) (ne_of_gt hdiff)),
    Real.log_mul (Real.exp_ne_zero 1)
    (div_ne_zero (ne_of_gt hrange2) (ne_of_gt hdiff)),
    Real.log_exp]
  linarith

theorem clause23_lemma56_rank_log (ra rb : ℕ) :
    lemma56RankLog ra rb = Real.log (min ra rb) := rfl

theorem clause23_lemma56_rank_log_lower_def (ra rb m : ℕ) :
    lemma56RankLogLower ra rb m = Real.log (min (min ra rb) m) := rfl

theorem clause23_lemma56_rank_log_lower (ra rb m : ℕ) (hm0 : 0 < m) (hm : m ≤ min ra rb) :
    Real.log (m : ℝ) ≤ lemma56RankLog ra rb := by
  unfold lemma56RankLog
  have hcast : (m : ℝ) ≤ min (↑ra : ℝ) (↑rb : ℝ) := by
    have h1 : (m : ℝ) ≤ ↑(min ra rb) := Nat.cast_le.mpr hm
    rwa [Nat.cast_min] at h1
  exact Real.log_le_log (by exact_mod_cast hm0) hcast

theorem clause23_classical_output_shape {C RS : Type} [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS]
    (f0 : ℂ) (R : Matrix RS C ℂ) (u : Matrix RS RS ℂ) :
    classicalOutput f0 R u = Rᴴ * u * R + f0 • (1 : Matrix C C ℂ) := rfl

theorem clause23_output_sq_queries_le_time (r c perSample : ℕ) (hper : 1 ≤ perSample) :
    outputSqQueries r c ≤ lemma49SketchTime r c perSample := by
  unfold outputSqQueries lemma49SketchTime
  have h := Nat.mul_le_mul_left (r + c) hper
  simpa using! h

theorem clause23_output_ram_le_bit (r c n w : ℕ) (hw : 1 ≤ w) :
    outputRamOps r c n ≤ outputBitTime r c n w := by
  have h := Nat.mul_le_mul_left (outputRamOps r c n) hw
  simpa [Nat.mul_comm, Nat.mul_one] using! h

theorem clause23_function_evaluation_cost (s : ℕ) :
    functionEvaluationCost s = s * s := rfl

theorem clause23_backend_query_cost (r c s : ℕ) :
    backendQueryCost r c s = r + c + s * s := rfl

theorem clause23_backend_ram_le_bit (r c s n w : ℕ) (hw : 1 ≤ w) :
    backendRamWords r c s n ≤ backendBitTime r c s n w := by
  have h := Nat.mul_le_mul_left (backendRamWords r c s n) hw
  simpa [Nat.mul_comm, Nat.mul_one] using! h

theorem clause23_frame_power_le_one (k m : ℕ) (hm : 0 < m) (hkm : k ≤ m) :
    framePower k m ≤ 1 := by
  unfold framePower
  rw [div_le_one (by exact_mod_cast hm)]
  exact_mod_cast hkm

theorem clause23_numerical_svd_iterations_pos (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < numericalSvdIterations ε := by
  unfold numericalSvdIterations
  apply Real.log_pos
  rw [lt_div_iff₀ hε]
  linarith

theorem clause23_numerical_svd_relative_error (ε : ℝ) :
    numericalSvdRelativeError ε = ε := rfl

theorem clause23_th71_two_stage_factor (φ L normA normAF ε δ : ℝ) :
    th71ColSamples φ L normA normAF ε δ * (normAF ^ 2)
      = th71RowSamples φ L normA normAF ε δ * (normA ^ 2) := by
  unfold th71ColSamples th71RowSamples
  ring

theorem clause23_th72_vs_th71_factor (φ L normA normAF ε δ : ℝ) (hε : ε ≠ 0) :
    th72RowSamples φ L normA normAF ε δ * (normAF ^ 2 * ε ^ 4)
      = th71RowSamples φ L normA normAF ε δ * (normA ^ 2 * L ^ 4) := by
  have hε2 : ε ^ 2 ≠ 0 := by rw [pow_two]; exact mul_ne_zero hε hε
  have hε6 : ε ^ 6 ≠ 0 := by
    have h : ε ^ 6 = ε ^ 2 * ε ^ 2 * ε ^ 2 := by ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero hε2 hε2) hε2
  unfold th72RowSamples th71RowSamples
  have e1 : (φ ^ 2 * normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6 * Real.log (1 / δ))
        * (normAF ^ 2 * ε ^ 4)
      = (φ ^ 2 * normA ^ 4 * normAF ^ 2 * L ^ 6 * Real.log (1 / δ) * normAF ^ 2 * ε ^ 4) / ε ^ 6 := by
    ring
  have e2 : (φ ^ 2 * L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2 * Real.log (1 / δ))
        * (normA ^ 2 * L ^ 4)
      = (φ ^ 2 * L ^ 2 * normA ^ 2 * normAF ^ 4 * Real.log (1 / δ) * normA ^ 2 * L ^ 4) / ε ^ 2 := by
    ring
  rw [e1, e2]
  exact (div_eq_div_iff hε6 hε2).2 (by ring)

theorem clause23_th72_rank_budget (L normAF ε : ℝ) :
    th72RankSamples L normAF ε = normAF ^ 2 * L ^ 2 / ε ^ 2 := rfl

theorem clause23_markov_row_control_not_tighter (φ normA normAF σk ε δ : ℝ)
    (hA : 0 ≤ normA) (hAF : 0 ≤ normAF) (hσ : 0 < σk) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hAFsq : normA ≤ normAF) (hεσ : ε ≤ σk ^ 2) :
    opOptimalRowSamples φ normA normAF σk δ ≤ markovRowSamples φ normAF ε δ := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; simpa using! hδ1.le)
  have hinner : normA * ε ≤ normAF * σk ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hεσ hA
    have h2 := mul_le_mul_of_nonneg_right hAFsq (sq_nonneg σk)
    nlinarith [h, h2]
  have hmul : normA * normAF * ε ≤ normAF ^ 2 * σk ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinner hAF
    nlinarith [h]
  have hsq : (normA * normAF * ε) ^ 2 ≤ (normAF ^ 2 * σk ^ 2) ^ 2 := by
    nlinarith [hmul, mul_nonneg (mul_nonneg hA hAF) hε.le,
      mul_nonneg (sq_nonneg normAF) (sq_nonneg σk)]
  have hkey : normA ^ 2 * normAF ^ 2 * ε ^ 2 ≤ normAF ^ 4 * σk ^ 4 := by
    nlinarith [hsq]
  have hcore : normA ^ 2 * normAF ^ 2 / σk ^ 4 ≤ normAF ^ 4 / ε ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact hkey
  have hmul : φ ^ 2 * (normA ^ 2 * normAF ^ 2 / σk ^ 4)
      ≤ φ ^ 2 * (normAF ^ 4 / ε ^ 2) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg φ)
  have hstep : (φ ^ 2 * (normA ^ 2 * normAF ^ 2 / σk ^ 4)) * Real.log (1 / δ)
      ≤ (φ ^ 2 * (normAF ^ 4 / ε ^ 2)) * Real.log (1 / δ) :=
    mul_le_mul_of_nonneg_right hmul hlog
  unfold opOptimalRowSamples markovRowSamples lemma414RowSamples
  calc (φ ^ 2 * normA ^ 2 * normAF ^ 2 / σk ^ 4) * Real.log (1 / δ)
      = φ ^ 2 * (normA ^ 2 * normAF ^ 2 / σk ^ 4) * Real.log (1 / δ) := by ring
    _ ≤ φ ^ 2 * (normAF ^ 4 / ε ^ 2) * Real.log (1 / δ) := hstep
    _ = (φ ^ 2 * normAF ^ 4 / ε ^ 2) * Real.log (1 / δ) := by ring

theorem clause23_qml_application_endpoint (φ L normA normAF ε δ : ℝ) :
    qmlApplicationSamples φ L normA normAF ε δ = th71RowSamples φ L normA normAF ε δ := rfl

theorem clause23_mmw_application_endpoint (φ L normA normAF ε δ : ℝ) :
    mmwApplicationSamples φ L normA normAF ε δ = th71ColSamples φ L normA normAF ε δ := rfl

theorem clause23_sdp_application_endpoint (φ L normA normAF ε δ : ℝ) :
    sdpApplicationSamples φ L normA normAF ε δ = th72RowSamples φ L normA normAF ε δ := rfl

theorem clause23_sdp_application_not_tighter (φ L normA normAF ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (htrade : normA ^ 2 * L ^ 4 ≥ normAF ^ 2 * ε ^ 4) :
    qmlApplicationSamples φ L normA normAF ε δ ≤ sdpApplicationSamples φ L normA normAF ε δ := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; simpa using! hδ1.le)
  have hkey : L ^ 2 * normA ^ 2 * normAF ^ 2 * ε ^ 4 ≤ normA ^ 4 * L ^ 6 := by
    have h := mul_le_mul_of_nonneg_left htrade (mul_nonneg (sq_nonneg normA) (sq_nonneg L))
    nlinarith [h]
  have hcore : L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2
      ≤ normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hε) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hkey
      (mul_nonneg (sq_nonneg normAF) (sq_nonneg ε))
    nlinarith [hmul]
  have hmulφ : φ ^ 2 * (L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2)
      ≤ φ ^ 2 * (normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg φ)
  have hlogstep : (φ ^ 2 * (L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2)) * Real.log (1 / δ)
      ≤ (φ ^ 2 * (normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6)) * Real.log (1 / δ) :=
    mul_le_mul_of_nonneg_right hmulφ hlog
  unfold qmlApplicationSamples sdpApplicationSamples th71RowSamples th72RowSamples
  calc (φ ^ 2 * L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2) * Real.log (1 / δ)
      = φ ^ 2 * (L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2) * Real.log (1 / δ) := by ring
    _ ≤ φ ^ 2 * (normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6) * Real.log (1 / δ) := hlogstep
    _ = (φ ^ 2 * normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6) * Real.log (1 / δ) := by ring

theorem clause23_two_sketch_row_budget_has_rank_log (L ε φ δ E : ℝ) (rank : ℕ) :
    requiredRowSamples L ε φ δ E rank
      = 32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2 * E ^ 2 / ε ^ 2 := rfl

theorem clause23_rank_log_factor_ge_one (rank : ℕ) : 1 ≤ rankLogFactor rank := by
  have hnonneg : (0 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast Nat.zero_le rank
  unfold rankLogFactor
  have hlog : 0 ≤ Real.log (1 + (rank : ℝ)) := Real.log_nonneg (by linarith)
  linarith

theorem clause25_endpoint {C RS : Type} [Fintype C] [DecidableEq C] [Fintype RS]
    [DecidableEq RS]
    (φ ε δ normA normAF L : ℝ) (r c perSample n w : ℕ) (η₁ η₂ τ α : ℝ) (k m : ℕ)
    (ra rb : ℕ) (a b diff : ℝ) (f0 : ℂ) (R : Matrix RS C ℂ) (u : Matrix RS RS ℂ)
    (hε : 0 < ε) (hα : 0 < α) (hab : a ≤ b) (hdiff : 0 < diff)
    (hdiffle : diff ≤ b - a) (hm : 0 < m) (hkm : k ≤ m) (hper : 1 ≤ perSample)
    (hw : 1 ≤ w) (hεne : ε ≠ 0) :
    lemma49TotalSamples φ ε δ = 2 * lemma49RowSamples φ ε δ ∧
      (lemma49SampleBudgetMul φ ε δ r ↔ lemma49RowSamples φ ε δ ≤ r) ∧
      lemma414CutoffBudget η₁ η₂ = 2 * η₁ + 2 * η₂ ∧
      (lemma414IsometryBudget η₂ α ≤ τ ^ 2 ↔ η₂ ≤ τ ^ 2 * α) ∧
      1 ≤ lemma55LogFactor a b diff ∧
      lemma56RankLog ra rb = Real.log (min ra rb) ∧
      classicalOutput f0 R u = Rᴴ * u * R + f0 • (1 : Matrix C C ℂ) ∧
      outputSqQueries r c ≤ lemma49SketchTime r c perSample ∧
      outputRamOps r c n ≤ outputBitTime r c n w ∧
      framePower k m ≤ 1 ∧
      numericalSvdRelativeError ε = ε ∧
      th71ColSamples φ L normA normAF ε δ * (normAF ^ 2)
        = th71RowSamples φ L normA normAF ε δ * (normA ^ 2) ∧
      th72RankSamples L normAF ε = normAF ^ 2 * L ^ 2 / ε ^ 2 ∧
      qmlApplicationSamples φ L normA normAF ε δ = th71RowSamples φ L normA normAF ε δ ∧
      th72RowSamples φ L normA normAF ε δ * (normAF ^ 2 * ε ^ 4)
        = th71RowSamples φ L normA normAF ε δ * (normA ^ 2 * L ^ 4) := by
  refine And.intro (clause23_lemma49_total_is_two_row φ ε δ) ?_
  refine And.intro (clause23_lemma49_budget_iff φ ε δ hε r) ?_
  refine And.intro (clause23_lemma414_cutoff_budget η₁ η₂) ?_
  refine And.intro (clause23_lemma414_isometry_budget_iff η₂ α τ hα) ?_
  refine And.intro (clause23_lemma55_log_factor_ge_one a b diff hab hdiff hdiffle) ?_
  refine And.intro (clause23_lemma56_rank_log ra rb) ?_
  refine And.intro (clause23_classical_output_shape f0 R u) ?_
  refine And.intro (clause23_output_sq_queries_le_time r c perSample hper) ?_
  refine And.intro (clause23_output_ram_le_bit r c n w hw) ?_
  refine And.intro (clause23_frame_power_le_one k m hm hkm) ?_
  refine And.intro (clause23_numerical_svd_relative_error ε) ?_
  refine And.intro (clause23_th71_two_stage_factor φ L normA normAF ε δ) ?_
  refine And.intro (clause23_th72_rank_budget L normAF ε) ?_
  refine And.intro (clause23_qml_application_endpoint φ L normA normAF ε δ) ?_
  exact clause23_th72_vs_th71_factor φ L normA normAF ε δ hεne

end StageBSQMATRIXFUNCTION
end ConstructionStageB
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
