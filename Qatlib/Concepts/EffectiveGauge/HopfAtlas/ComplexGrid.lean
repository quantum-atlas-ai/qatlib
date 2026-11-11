/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ComplexTensor

/-!
# Complex Grid

Hopf Atlas constructions for Effective Gauge.
Defines `complexGridAverage`.
Proves `complexRangeSum_norm_le`, `complexGridAverage_sub_bound`, `complexMeanTensorLeftSum_eq_grid`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of complex Grid Average in the Hopf Atlas construction. -/
def complexGridAverage (N : ℕ) (a : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ((N : ℝ)^3)⁻¹ • (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N, a k l m)

/-- Original `complexRangeSum_norm_le` guarantee for the `ComplexGrid` construction; the complete source hypotheses are retained. -/
private theorem complexRangeSum_norm_le (N : ℕ) (a : ℕ → ℂ) (E : ℝ)
    (ha : ∀ k, k<N → ‖a k‖ ≤ E) : ‖∑ k ∈ Finset.range N, a k‖ ≤ (N : ℝ)*E := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, E := by
      apply Finset.sum_le_sum
      intro k hk
      exact ha k (Finset.mem_range.mp hk)
    _ = _ := by simp

/-- Accuracy is required only at the finite executed grid, not at arbitrary
real points or for an interpolated approximate function. -/
theorem complexGridAverage_sub_bound (N : ℕ) (hN : 0<N) (a b : ℕ → ℕ → ℕ → ℂ)
    (E : ℝ) (hab : ∀ k, k<N → ∀ l, l<N → ∀ m, m<N → ‖a k l m-b k l m‖ ≤ E) :
    ‖complexGridAverage N a-complexGridAverage N b‖ ≤ E := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hs : ‖∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (a k l m-b k l m)‖ ≤ (N : ℝ)^3*E := by
    calc
      _ ≤ (N : ℝ)*((N : ℝ)*((N : ℝ)*E)) := by
        apply complexRangeSum_norm_le N
        intro k hk
        apply complexRangeSum_norm_le N
        intro l hl
        exact complexRangeSum_norm_le N _ E (hab k hk l hl)
      _ = _ := by ring
  rw [complexGridAverage,complexGridAverage,← smul_sub]
  simp_rw [← Finset.sum_sub_distrib]
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ)^3))]
  calc
    _ ≤ ((N : ℝ)^3)⁻¹*((N : ℝ)^3*E) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = E := by rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 3 hn.ne'),one_mul]

/-- Original `complexMeanTensorLeftSum_eq_grid` guarantee for the `ComplexGrid` construction; the complete source hypotheses are retained. -/
theorem complexMeanTensorLeftSum_eq_grid (N : ℕ) (f : MeanTensorPoint → ℂ) :
    complexMeanTensorLeftSum N f=complexGridAverage N
      (fun k l m => f ((k : ℝ)/(N : ℝ),(l : ℝ)/(N : ℝ),(m : ℝ)/(N : ℝ))) := by
  simp only [complexMeanTensorLeftSum,complexMeanLeftSum,complexGridAverage]
  simp_rw [← Finset.smul_sum]
  simp only [smul_smul]
  congr 1
  by_cases hn : (N : ℝ)=0 <;> field_simp [hn]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
