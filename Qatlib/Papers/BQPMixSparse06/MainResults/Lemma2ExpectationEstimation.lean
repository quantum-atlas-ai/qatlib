/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Qatlib.Papers.BQPMixSparse06.MainResults

theorem hoeffding_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) {a b : ℝ} (hmes : ∀ i, AEMeasurable (X i) μ)
    (hmem : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, (X i ω - μ[X i])|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) := by
  classical
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, (X i ω - μ[X i]) with hS
  set c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2 with hc
  have hcR : ((c : ℝ)) = ((‖b - a‖₊ : ℝ) / 2) ^ 2 := by
    simp [c]
  have hsubG : ∀ i, HasSubgaussianMGF (fun ω => X i ω - μ[X i]) c μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X i) (hmes i) (hmem i)
    simpa [c] using h
  have hindep : iIndepFun (fun i ω => X i ω - μ[X i]) μ :=
    h_indep.comp (fun i x => x - ∫ y, X i y ∂μ)
      (fun i => measurable_id.sub measurable_const)

  have hA : μ.real {ω | ε ≤ S ω} ≤
      Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) := by
    have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (μ := μ) (X := fun i ω => X i ω - μ[X i]) hindep (c := c) (n := n)
      (fun i _ => hsubG i) hε
    rw [hcR] at h
    simpa [S] using h

  have hindep' : iIndepFun (fun i ω => -(X i ω - μ[X i])) μ :=
    h_indep.comp (fun i x => -(x - ∫ y, X i y ∂μ))
      (fun i => (measurable_id.sub measurable_const).neg)
  have hsubG' : ∀ i, HasSubgaussianMGF (fun ω => -(X i ω - μ[X i])) c μ :=
    fun i => (hsubG i).neg
  have hB : μ.real {ω | ε ≤ -S ω} ≤
      Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) := by
    have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (μ := μ) (X := fun i ω => -(X i ω - μ[X i])) hindep' (c := c) (n := n)
      (fun i _ => hsubG' i) hε
    rw [hcR] at h
    simpa [S] using h

  have hsub : {ω | ε ≤ |S ω|} ⊆ {ω | ε ≤ S ω} ∪ {ω | ε ≤ -S ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_total 0 (S ω) with hpos | hneg
    · left; rwa [abs_of_nonneg hpos] at hω
    · right
      rwa [abs_of_nonpos hneg] at hω
  calc μ.real {ω | ε ≤ |S ω|}
      ≤ μ.real ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -S ω}) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | ε ≤ S ω} + μ.real {ω | ε ≤ -S ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) +
          Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) :=
        add_le_add hA hB
    _ = 2 * Real.exp (-ε ^ 2 / (2 * (n : ℝ) * ((‖b - a‖₊ : ℝ) / 2) ^ 2)) := by
        ring

theorem lemma2_sample_size_e {a b ε α : ℝ} (hab : a < b) (hε : 0 < ε)
    (hα : 0 < α) (hα2 : α ≤ 2) {n : ℕ} (h1n : 1 ≤ n)
    (hn : (b - a) ^ 2 * Real.log (2 / α) / (2 * ε ^ 2) ≤ n) :
    2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2) / (b - a) ^ 2) ≤ α := by
  have hb : 0 < b - a := by linarith
  have h2e : 0 < 2 * ε ^ 2 := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hnpos : 0 < (n : ℝ) := by linarith

  have hmul : Real.log (2 / α) ≤ 2 * (n : ℝ) * ε ^ 2 / (b - a) ^ 2 := by
    have hposc : 0 ≤ 2 * ε ^ 2 / (b - a) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hn hposc
    have hbne : (b - a) ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
    have h2ene : 2 * ε ^ 2 ≠ 0 := ne_of_gt h2e
    have h2 : (b - a) ^ 2 * Real.log (2 / α) / (2 * ε ^ 2) * (2 * ε ^ 2 / (b - a) ^ 2) =
        Real.log (2 / α) := by
      field_simp
    have h3 : (n : ℝ) * (2 * ε ^ 2 / (b - a) ^ 2) =
        2 * (n : ℝ) * ε ^ 2 / (b - a) ^ 2 := by ring
    linarith [h1, h2, h3]

  have hexp_le : Real.exp (-(2 * (n : ℝ) * ε ^ 2) / (b - a) ^ 2) ≤ α / 2 := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < α / 2)]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (α / 2) = -Real.log (2 / α) := by
      rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hα)]
      ring
    rw [hlog]
    have hgoal : -(2 * (n : ℝ) * ε ^ 2) / (b - a) ^ 2 =
        -(2 * (n : ℝ) * ε ^ 2 / (b - a) ^ 2) := by ring
    rw [hgoal]
    linarith
  have : 2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2) / (b - a) ^ 2) ≤ 2 * (α / 2) :=
    mul_le_mul_of_nonneg_left hexp_le (by norm_num)
  linarith

theorem lemma2_error_budget (E target M K ε θ η D : ℝ) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hθ : θ = ε / 6)
    (hη : η = ε / (6 * Real.pi)) (hD : D ≤ ε / 3)
    (hideal : |E - target| ≤ (2 * θ + D) * M + 2 * Real.pi * K * η) :
    |E - target| ≤ ε * (M + K) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hθ' : 2 * θ * M = ε / 3 * M := by
    rw [hθ]; ring
  have hη' : 2 * Real.pi * K * η = ε / 3 * K := by
    rw [hη]
    field_simp
    ring
  have hD' : D * M ≤ ε / 3 * M := mul_le_mul_of_nonneg_right hD hM
  have hεK : 0 ≤ ε * K := mul_nonneg hε hK
  have hεM : 0 ≤ ε * M := mul_nonneg hε hM
  have h1 : ε / 3 * M ≤ ε * (M + K) / 3 := by nlinarith
  have h2 : ε / 3 * K ≤ ε * (M + K) / 3 := by nlinarith
  have hexp : (2 * θ + D) * M + 2 * Real.pi * K * η =
      2 * θ * M + D * M + 2 * Real.pi * K * η := by ring
  linarith [hideal, hexp, hθ', hη', hD', h1, h2]

theorem lemma2_expectation_estimation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (est : Ω → ℝ) (mean target ε ε₁ α M K : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (harith : ε + ε₁ ≤ ε * (M + K)) (hgap : |mean - target| ≤ ε₁)
    (hprob : μ.real {ω | ε ≤ |est ω - mean|} ≤ α) :
    μ.real {ω | ε * (M + K) ≤ |est ω - target|} ≤ α := by
  refine le_trans (measureReal_mono ?_) hprob
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push_neg at hcon
  have h1 : |est ω - target| ≤ |est ω - mean| + |mean - target| := by
    have h := abs_add_le (est ω - mean) (mean - target)
    simpa using h
  linarith

end Qatlib.Papers.BQPMixSparse06.MainResults
