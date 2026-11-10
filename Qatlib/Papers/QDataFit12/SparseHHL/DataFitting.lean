/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDataFit12.SparseHHL.DataFittingDefs
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL

theorem clause22_concise_tomography_budget (M M' f f' : ℕ) (hM : M ≤ M') (hf : f ≤ f') :
    conciseTomographySettings M ≤ conciseTomographySettings M' ∧
      conciseTomographyTotal M f ≤ conciseTomographyTotal M' f' := by
  have hle : (M + 1 : ℝ) ≤ (M' + 1 : ℝ) := by
    have h1 : M + 1 ≤ M' + 1 := by omega
    exact_mod_cast h1
  have hlog : Real.log (M + 1) ≤ Real.log (M' + 1) :=
    Real.log_le_log (by positivity) hle
  have hlog0 : 0 ≤ Real.log (M + 1) := by
    have h1 : (1:ℝ) ≤ (M + 1 : ℝ) := by
      have h2 : (1:ℕ) ≤ M + 1 := by omega
      exact_mod_cast h2
    exact Real.log_nonneg (x := (M + 1 : ℝ)) h1
  have hlog0' : 0 ≤ Real.log (M' + 1) := by
    have h1 : (1:ℝ) ≤ (M' + 1 : ℝ) := by
      have h2 : (1:ℕ) ≤ M' + 1 := by omega
      exact_mod_cast h2
    exact Real.log_nonneg (x := (M' + 1 : ℝ)) h1
  have hsq : Real.log (M + 1) ^ 2 ≤ Real.log (M' + 1) ^ 2 :=
    (sq_le_sq₀ hlog0 hlog0').mpr hlog
  have hM' : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM
  have hf' : (f : ℝ) ≤ (f' : ℝ) := by exact_mod_cast hf
  constructor
  · simp only [conciseTomographySettings]
    exact mul_le_mul hM' hsq (sq_nonneg _) (by positivity)
  · simp only [conciseTomographyTotal, conciseTomographySettings]
    exact mul_le_mul (mul_le_mul hM' hsq (sq_nonneg _) (by positivity)) hf'
      (by positivity) (by positivity)

theorem clause22_endpoint :
    (∀ M M' f f' : ℕ, M ≤ M' → f ≤ f' →
      conciseTomographySettings M ≤ conciseTomographySettings M' ∧
        conciseTomographyTotal M f ≤ conciseTomographyTotal M' f') ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012.DataFitActualParameterRestricted ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012.DataFitActualQualityRestricted := by
  refine ⟨fun M M' f f' hM hf => clause22_concise_tomography_budget M M' f f' hM hf,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.dataFitActualParameterRestricted,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.dataFitActualQualityRestricted⟩

theorem clause23_sparse_fit_headline (s s' κ κ' : ℕ) (hs : s ≤ s') (hκ : κ ≤ κ') :
    sparseFitHeadline s κ ≤ sparseFitHeadline s' κ' := by
  simp only [sparseFitHeadline]
  have h3 : s ^ 3 ≤ s' ^ 3 := Nat.pow_le_pow_left hs 3
  have h6 : κ ^ 6 ≤ κ' ^ 6 := Nat.pow_le_pow_left hκ 6
  exact Nat.mul_le_mul h3 h6

theorem clause23_endpoint :
    ∀ s s' κ κ' : ℕ, s ≤ s' → κ ≤ κ' →
      sparseFitHeadline s κ ≤ sparseFitHeadline s' κ' :=
  fun s s' κ κ' hs hκ => clause23_sparse_fit_headline s s' κ κ' hs hκ

private theorem clause23_inv_mono (a b : ℝ) (ha : 0 < a) (hle : a ≤ b) (c : ℝ)
    (hc : 0 ≤ c) : c / b ≤ c / a := by
  have hinv : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hle
  have h2 : b⁻¹ ≤ a⁻¹ := by simpa [one_div] using! hinv
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h2 hc

private theorem clause23_log_nonneg (N : ℕ) : 0 ≤ Real.log (N + 1) := by
  have h1 : (1:ℝ) ≤ (N:ℝ) + 1 := by
    have h2 : (1:ℕ) ≤ N + 1 := by omega
    exact_mod_cast h2
  exact Real.log_nonneg h1

theorem clause23_fit_headline_anti_mono_eps (N s κ : ℕ) (ε ε' : ℝ) (hε : 0 < ε)
    (hle : ε ≤ ε') : fitHeadlineCost N s κ ε' ≤ fitHeadlineCost N s κ ε := by
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6 :=
    mul_nonneg (mul_nonneg (clause23_log_nonneg N) (pow_nonneg (Nat.cast_nonneg s) 3))
      (pow_nonneg (Nat.cast_nonneg κ) 6)
  unfold fitHeadlineCost
  exact clause23_inv_mono ε ε' hε hle _ hC

theorem clause23_simulation_headline_anti_mono_eps (N s κ : ℕ) (ε ε' : ℝ) (hε : 0 < ε)
    (hle : ε ≤ ε') :
    simulationHeadlineCost N s κ ε' ≤ simulationHeadlineCost N s κ ε := by
  have hsq : ε ^ 2 ≤ ε' ^ 2 := pow_le_pow_left₀ (le_of_lt hε) hle 2
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6 :=
    mul_nonneg (mul_nonneg (clause23_log_nonneg N) (Nat.cast_nonneg s))
      (pow_nonneg (Nat.cast_nonneg κ) 6)
  unfold simulationHeadlineCost
  exact clause23_inv_mono (ε ^ 2) (ε' ^ 2) (sq_pos_of_pos hε) hsq _ hC

theorem clause23_readout_headline_anti_mono_eps (N s κ M' : ℕ) (ε ε' δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hle : ε ≤ ε') :
    readoutHeadlineCost N s κ M' ε' δ ≤ readoutHeadlineCost N s κ M' ε δ := by
  have hA : ε * δ ^ 2 ≤ ε' * δ ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  have hB : ε ^ 3 ≤ ε' ^ 3 := pow_le_pow_left₀ (le_of_lt hε) hle 3
  have hκ4 : 0 ≤ (κ : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg κ) 4
  have hM : 0 ≤ (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg M') 2) (pow_nonneg (Nat.cast_nonneg κ) 6)
  have hsum : (κ : ℝ) ^ 4 / (ε' * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε' ^ 3 ≤
      (κ : ℝ) ^ 4 / (ε * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3 := by
    have h1 := clause23_inv_mono (ε * δ ^ 2) (ε' * δ ^ 2)
      (mul_pos hε (sq_pos_of_pos hδ)) hA _ hκ4
    have h2 := clause23_inv_mono (ε ^ 3) (ε' ^ 3)
      (mul_pos (sq_pos_of_pos hε) hε) hB _ hM
    exact add_le_add h1 h2
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) ^ 3 :=
    mul_nonneg (clause23_log_nonneg N) (pow_nonneg (Nat.cast_nonneg s) 3)
  unfold readoutHeadlineCost
  exact mul_le_mul_of_nonneg_left hsum hC

theorem clause23_readout_headline_anti_mono_delta (N s κ M' : ℕ) (ε δ δ' : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ' : 0 < δ') (hle : δ ≤ δ') :
    readoutHeadlineCost N s κ M' ε δ' ≤ readoutHeadlineCost N s κ M' ε δ := by
  have hsq : δ ^ 2 ≤ δ' ^ 2 := (sq_le_sq₀ (le_of_lt hδ) (le_of_lt hδ')).mpr hle
  have hA : ε * δ ^ 2 ≤ ε * δ' ^ 2 := mul_le_mul_of_nonneg_left hsq (le_of_lt hε)
  have hκ4 : 0 ≤ (κ : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg κ) 4
  have hM : 0 ≤ (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg M') 2) (pow_nonneg (Nat.cast_nonneg κ) 6)
  have hsum : (κ : ℝ) ^ 4 / (ε * δ' ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3 ≤
      (κ : ℝ) ^ 4 / (ε * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3 := by
    have h1 := clause23_inv_mono (ε * δ ^ 2) (ε * δ' ^ 2)
      (mul_pos hε (sq_pos_of_pos hδ)) hA _ hκ4
    have h2 := le_refl ((M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3)
    exact add_le_add h1 h2
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) ^ 3 :=
    mul_nonneg (clause23_log_nonneg N) (pow_nonneg (Nat.cast_nonneg s) 3)
  unfold readoutHeadlineCost
  exact mul_le_mul_of_nonneg_left hsum hC

private theorem clause23_log_mono (N N' : ℕ) (hN : N ≤ N') :
    Real.log (N + 1) ≤ Real.log (N' + 1) ∧ 0 ≤ Real.log (N' + 1) := by
  have hle : (N + 1 : ℝ) ≤ (N' + 1 : ℝ) := by
    have h1 : N + 1 ≤ N' + 1 := by omega
    exact_mod_cast h1
  have hlog : Real.log (N + 1) ≤ Real.log (N' + 1) :=
    Real.log_le_log (by positivity) hle
  have h0' : 0 ≤ Real.log (N' + 1) := Real.log_nonneg (by
    have h1 : (1:ℝ) ≤ (N' + 1 : ℝ) := by
      have h2 : (1:ℕ) ≤ N' + 1 := by omega
      exact_mod_cast h2
    exact h1)
  exact ⟨hlog, h0'⟩

theorem clause23_fit_headline_mono (N N' s s' κ κ' : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') :
    fitHeadlineCost N s κ ε ≤ fitHeadlineCost N' s' κ' ε := by
  have hlog := clause23_log_mono N N' hN
  have h3 : (s : ℝ) ^ 3 ≤ (s' : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) 3
  have h6 : (κ : ℝ) ^ 6 ≤ (κ' : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hκ) 6
  have hnum : Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6
      ≤ Real.log (N' + 1) * (s' : ℝ) ^ 3 * (κ' : ℝ) ^ 6 := by
    calc Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6
        = (Real.log (N + 1) * (s : ℝ) ^ 3) * (κ : ℝ) ^ 6 := by ring
      _ ≤ (Real.log (N' + 1) * (s' : ℝ) ^ 3) * (κ' : ℝ) ^ 6 := by
        refine mul_le_mul ?_ h6 (pow_nonneg (Nat.cast_nonneg κ) 6)
          (mul_nonneg hlog.2 (pow_nonneg (Nat.cast_nonneg s') 3))
        exact mul_le_mul hlog.1 h3 (pow_nonneg (Nat.cast_nonneg s) 3) hlog.2
      _ = Real.log (N' + 1) * (s' : ℝ) ^ 3 * (κ' : ℝ) ^ 6 := by ring
  have hinv : (0:ℝ) ≤ (ε : ℝ)⁻¹ := by positivity
  unfold fitHeadlineCost
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum hinv

theorem clause23_simulation_headline_mono (N N' s s' κ κ' : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') :
    simulationHeadlineCost N s κ ε ≤ simulationHeadlineCost N' s' κ' ε := by
  have hlog := clause23_log_mono N N' hN
  have h1 : (s : ℝ) ≤ (s' : ℝ) := by exact_mod_cast hs
  have h6 : (κ : ℝ) ^ 6 ≤ (κ' : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hκ) 6
  have hnum : Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6
      ≤ Real.log (N' + 1) * (s' : ℝ) * (κ' : ℝ) ^ 6 := by
    calc Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6
        = (Real.log (N + 1) * (s : ℝ)) * (κ : ℝ) ^ 6 := by ring
      _ ≤ (Real.log (N' + 1) * (s' : ℝ)) * (κ' : ℝ) ^ 6 := by
        refine mul_le_mul ?_ h6 (pow_nonneg (Nat.cast_nonneg κ) 6)
          (mul_nonneg hlog.2 (Nat.cast_nonneg s'))
        exact mul_le_mul hlog.1 h1 (Nat.cast_nonneg s) hlog.2
      _ = Real.log (N' + 1) * (s' : ℝ) * (κ' : ℝ) ^ 6 := by ring
  have hinv : (0:ℝ) ≤ (ε ^ 2 : ℝ)⁻¹ := by positivity
  unfold simulationHeadlineCost
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum hinv

theorem clause23_readout_headline_mono (N N' s s' κ κ' M M' : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') (hM : M ≤ M') :
    readoutHeadlineCost N s κ M ε δ ≤ readoutHeadlineCost N' s' κ' M' ε δ := by
  have hlog := clause23_log_mono N N' hN
  have h3 : (s : ℝ) ^ 3 ≤ (s' : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) 3
  have h4 : (κ : ℝ) ^ 4 ≤ (κ' : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hκ) 4
  have h6 : (κ : ℝ) ^ 6 ≤ (κ' : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hκ) 6
  have hM2 : (M : ℝ) ^ 2 ≤ (M' : ℝ) ^ 2 := by
    have h1 : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM
    nlinarith [sq_nonneg (M' - M)]
  have hA : (κ : ℝ) ^ 4 * (ε * δ ^ 2)⁻¹
      ≤ (κ' : ℝ) ^ 4 * (ε * δ ^ 2)⁻¹ := by
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hB : ((M : ℝ) ^ 2 * (κ : ℝ) ^ 6) * (ε ^ 3)⁻¹
      ≤ ((M' : ℝ) ^ 2 * (κ' : ℝ) ^ 6) * (ε ^ 3)⁻¹ := by
    have hML : (M : ℝ) ^ 2 * (κ : ℝ) ^ 6 ≤ (M' : ℝ) ^ 2 * (κ' : ℝ) ^ 6 := by
      calc (M : ℝ) ^ 2 * (κ : ℝ) ^ 6 = ((M : ℝ) ^ 2) * (κ : ℝ) ^ 6 := by ring
        _ ≤ ((M' : ℝ) ^ 2) * (κ' : ℝ) ^ 6 := by
          refine mul_le_mul hM2 h6 (by positivity) (by positivity)
        _ = (M' : ℝ) ^ 2 * (κ' : ℝ) ^ 6 := by ring
    exact mul_le_mul_of_nonneg_right hML (by positivity)
  have hinner : (κ : ℝ) ^ 4 * (ε * δ ^ 2)⁻¹
        + ((M : ℝ) ^ 2 * (κ : ℝ) ^ 6) * (ε ^ 3)⁻¹
      ≤ (κ' : ℝ) ^ 4 * (ε * δ ^ 2)⁻¹
        + ((M' : ℝ) ^ 2 * (κ' : ℝ) ^ 6) * (ε ^ 3)⁻¹ := by
    linarith [hA, hB]
  have hX : Real.log (N + 1) * (s : ℝ) ^ 3
      ≤ Real.log (N' + 1) * (s' : ℝ) ^ 3 := by
    exact mul_le_mul hlog.1 h3 (pow_nonneg (Nat.cast_nonneg s) 3) hlog.2
  unfold readoutHeadlineCost
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul hX hinner ?_ ?_
  · have hp1 : (0:ℝ) ≤ (κ : ℝ) ^ 4 * (ε * δ ^ 2)⁻¹ := by positivity
    have hp2 : (0:ℝ) ≤ ((M : ℝ) ^ 2 * (κ : ℝ) ^ 6) * (ε ^ 3)⁻¹ := by positivity
    linarith
  · exact mul_nonneg hlog.2 (pow_nonneg (Nat.cast_nonneg s') 3)

theorem clause23_sparse_fit_query_cost_eq (M r k s κ : ℕ) :
    sparseFitQueryCost M r k s κ = dataFitQueryLedger M r k * sparseFitHeadline s κ := rfl

theorem clause23_sparse_fit_query_cost_dominates (M r k s κ : ℕ)
    (hM : 1 ≤ M) (hr : 1 ≤ r) :
    sparseFitHeadline s κ ≤ sparseFitQueryCost M r k s κ := by
  have h1 : 1 ≤ M * r := by
    have h2 : 1 * 1 ≤ M * r := Nat.mul_le_mul hM hr
    simpa using! h2
  have h2 : M * r ≤ dataFitQueryLedger M r k := dataFitQueryLedger_ge M r k
  have h3 : 1 ≤ dataFitQueryLedger M r k := by omega
  simp only [sparseFitQueryCost]
  have h4 := Nat.le_mul_of_pos_right (sparseFitHeadline s κ) h3
  simpa [Nat.mul_comm] using! h4

theorem clause23_sparse_fit_query_cost_mono (M M' r r' k k' s s' κ κ' : ℕ)
    (hM : M ≤ M') (hr : r ≤ r') (hk : k ≤ k') (hs : s ≤ s') (hκ : κ ≤ κ') :
    sparseFitQueryCost M r k s κ ≤ sparseFitQueryCost M' r' k' s' κ' := by
  simp only [sparseFitQueryCost]
  exact Nat.mul_le_mul (dataFitQueryLedger_mono M M' r r' k k' hM hr hk)
    (Nat.mul_le_mul (Nat.pow_le_pow_left hs 3) (Nat.pow_le_pow_left hκ 6))

theorem clause23_headline_endpoint :
    (∀ N N' s s' κ κ' : ℕ, ∀ (ε : ℝ), 0 < ε → N ≤ N' → s ≤ s' → κ ≤ κ' →
        fitHeadlineCost N s κ ε ≤ fitHeadlineCost N' s' κ' ε) ∧
      (∀ N N' s s' κ κ' : ℕ, ∀ (ε : ℝ), 0 < ε → N ≤ N' → s ≤ s' → κ ≤ κ' →
        simulationHeadlineCost N s κ ε ≤ simulationHeadlineCost N' s' κ' ε) ∧
      (∀ N N' s s' κ κ' M M' : ℕ, ∀ (ε δ : ℝ), 0 < ε → 0 < δ → N ≤ N' → s ≤ s' →
        κ ≤ κ' → M ≤ M' →
          readoutHeadlineCost N s κ M ε δ ≤ readoutHeadlineCost N' s' κ' M' ε δ) ∧
      (∀ M r k s κ : ℕ, 1 ≤ M → 1 ≤ r →
        sparseFitHeadline s κ ≤ sparseFitQueryCost M r k s κ) ∧
      (∀ M M' r r' k k' s s' κ κ' : ℕ, M ≤ M' → r ≤ r' → k ≤ k' → s ≤ s' → κ ≤ κ' →
        sparseFitQueryCost M r k s κ ≤ sparseFitQueryCost M' r' k' s' κ') ∧
      (∀ N s κ : ℕ, ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' →
        fitHeadlineCost N s κ ε' ≤ fitHeadlineCost N s κ ε) ∧
      (∀ N s κ : ℕ, ∀ ε ε' : ℝ, 0 < ε → ε ≤ ε' →
        simulationHeadlineCost N s κ ε' ≤ simulationHeadlineCost N s κ ε) ∧
      (∀ N s κ M' : ℕ, ∀ ε ε' δ : ℝ, 0 < ε → 0 < δ → ε ≤ ε' →
        readoutHeadlineCost N s κ M' ε' δ ≤ readoutHeadlineCost N s κ M' ε δ) ∧
      (∀ N s κ M' : ℕ, ∀ ε δ δ' : ℝ, 0 < ε → 0 < δ → δ ≤ δ' →
        readoutHeadlineCost N s κ M' ε δ' ≤ readoutHeadlineCost N s κ M' ε δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N N' s s' κ κ' ε hε hN hs hκ
    exact clause23_fit_headline_mono N N' s s' κ κ' ε hε hN hs hκ
  · intro N N' s s' κ κ' ε hε hN hs hκ
    exact clause23_simulation_headline_mono N N' s s' κ κ' ε hε hN hs hκ
  · intro N N' s s' κ κ' M M' ε δ hε hδ hN hs hκ hM
    exact clause23_readout_headline_mono N N' s s' κ κ' M M' ε δ hε hδ hN hs hκ hM
  · intro M r k s κ hM hr
    exact clause23_sparse_fit_query_cost_dominates M r k s κ hM hr
  · intro M M' r r' k k' s s' κ κ' hM hr hk hs hκ
    exact clause23_sparse_fit_query_cost_mono M M' r r' k k' s s' κ κ' hM hr hk hs hκ
  · intro N s κ ε ε' hε hle
    exact clause23_fit_headline_anti_mono_eps N s κ ε ε' hε hle
  · intro N s κ ε ε' hε hle
    exact clause23_simulation_headline_anti_mono_eps N s κ ε ε' hε hle
  · intro N s κ M' ε ε' δ hε hδ hle
    exact clause23_readout_headline_anti_mono_eps N s κ M' ε ε' δ hε hδ hle
  · intro N s κ M' ε δ δ' hε hδ hle
    exact clause23_readout_headline_anti_mono_delta N s κ M' ε δ δ' hε hδ
      (lt_of_lt_of_le hδ hle) hle

theorem clause24_general_data_loading (M M' s s' b b' : ℕ)
    (hM : M ≤ M') (hs : s ≤ s') (hb : b ≤ b') :
    M * dataLoadingGates s b ≤ M' * dataLoadingGates s' b' := by
  simp only [dataLoadingGates]
  exact Nat.mul_le_mul hM (Nat.mul_le_mul hs hb)

theorem clause24_endpoint :
    ∀ M M' s s' b b' : ℕ, M ≤ M' → s ≤ s' → b ≤ b' →
      M * dataLoadingGates s b ≤ M' * dataLoadingGates s' b' :=
  fun M M' s s' b b' hM hs hb => clause24_general_data_loading M M' s s' b b' hM hs hb

theorem clause25_phase_recovery_counts (b b' : ℕ) (hb : b ≤ b') :
    phaseRecoveryGateCount b ≤ phaseRecoveryBitCount b ∧
      phaseRecoveryGateCount b ≤ phaseRecoveryGateCount b' ∧
      phaseRecoveryBitCount b ≤ phaseRecoveryBitCount b' := by
  simp only [phaseRecoveryGateCount, phaseRecoveryBitCount]
  omega

theorem clause25_endpoint :
    ∀ b b' : ℕ, b ≤ b' →
      phaseRecoveryGateCount b ≤ phaseRecoveryBitCount b ∧
        phaseRecoveryGateCount b ≤ phaseRecoveryGateCount b' ∧
        phaseRecoveryBitCount b ≤ phaseRecoveryBitCount b' :=
  fun b b' hb => clause25_phase_recovery_counts b b' hb

theorem clause26_fresh_copy_total_cost (k : ℕ) (p c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hc : 0 ≤ c) :
    k * c ≤ freshCopyTotalCost k p c := by
  have hk : (k : ℝ) ≤ expectedFreshCopies k p := by
    rw [expectedFreshCopies]
    have h1 : (k : ℝ) * p ≤ (k : ℝ) := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [hp1]
    rw [le_div_iff₀ hp]
    exact h1
  rw [freshCopyTotalCost]
  have hprod : (k : ℝ) * c ≤ expectedFreshCopies k p * c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hc]
  exact hprod

theorem clause26_endpoint :
    ∀ k : ℕ, ∀ p c : ℝ, 0 < p → p ≤ 1 → 0 ≤ c → k * c ≤ freshCopyTotalCost k p c :=
  fun k p c hp hp1 hc => clause26_fresh_copy_total_cost k p c hp hp1 hc

theorem clause26_full_cost_dominates_ledger (k : ℕ) (p g b c : ℝ)
    (hp : 0 < p) (hg : 0 ≤ g) (hb : 0 ≤ b) :
    freshCopyTotalCost k p c ≤ freshCopyTotalCostFull k p g b c := by
  have h1 : expectedFreshCopies k p ≥ 0 := by
    unfold expectedFreshCopies
    positivity
  have h2 : c ≤ g + b + c := by linarith
  unfold freshCopyTotalCostFull freshCopyTotalCost
  exact mul_le_mul_of_nonneg_left h2 h1

theorem clause26_full_cost_unconditional (k : ℕ) (p g b c : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hg : 0 ≤ g) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    k * (g + b + c) ≤ freshCopyTotalCostFull k p g b c := by
  have hk : (k : ℝ) ≤ expectedFreshCopies k p := by
    rw [expectedFreshCopies]
    have h1 : (k : ℝ) * p ≤ (k : ℝ) := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [hp1]
    rw [le_div_iff₀ hp]
    exact h1
  have hsum : (0:ℝ) ≤ g + b + c := by linarith
  unfold freshCopyTotalCostFull
  have hmul : (k : ℝ) * (g + b + c) ≤ expectedFreshCopies k p * (g + b + c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hsum]
  exact hmul

theorem clause26_complete_endpoint :
    (∀ k : ℕ, ∀ p g b c : ℝ, 0 < p → 0 ≤ g → 0 ≤ b →
      freshCopyTotalCost k p c ≤ freshCopyTotalCostFull k p g b c) ∧
      (∀ k : ℕ, ∀ p g b c : ℝ, 0 < p → p ≤ 1 → 0 ≤ g → 0 ≤ b → 0 ≤ c →
        k * (g + b + c) ≤ freshCopyTotalCostFull k p g b c) := by
  refine ⟨?_, ?_⟩
  · intro k p g b c hp hg hb
    exact clause26_full_cost_dominates_ledger k p g b c hp hg hb
  · intro k p g b c hp hp1 hg hb hc
    exact clause26_full_cost_unconditional k p g b c hp hp1 hg hb hc

theorem clause27_concise_selection_samples (M' M'' : ℕ) (hM : M' ≤ M'') :
    conciseSelectionSamples M' ≤ conciseSelectionSamples M'' := by
  simp only [conciseSelectionSamples]
  exact hM

theorem clause27_endpoint :
    (∀ M' M'' : ℕ, M' ≤ M'' → conciseSelectionSamples M' ≤ conciseSelectionSamples M'') ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012.DataFitConciseSelectionRestricted := by
  refine ⟨fun M' M'' hM => clause27_concise_selection_samples M' M'' hM,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.dataFitConciseSelectionRestricted⟩

end Qatlib.Papers.QDataFit12.SparseHHL
