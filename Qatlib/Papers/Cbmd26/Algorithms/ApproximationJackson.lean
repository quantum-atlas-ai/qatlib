/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorExtraction
import Mathlib.Algebra.MvPolynomial.Equiv
set_option warningAsError false

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CBMD

open MeasureTheory Polynomial
open Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.JacksonApproximation
open scoped Classical BigOperators

theorem tensorJackson_unit_bound {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ z ∈ normalizedCube d, |f z| ≤ 1) (x : Fin d → ℝ) :
    |tensorConvolution K f x| ≤ 1 := by
  have h := norm_integral_le_of_norm_le (integrableOn_tensorJackson K d)
    (f := fun u => f (cosPoint (x - u)) * tensorJackson K d u)
    (Filter.Eventually.of_forall fun u => ?_)
  · simpa only [tensorConvolution, Real.norm_eq_abs,
      tensorJackson_integral_eq_one hK] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tensorJackson_nonneg hK u)]
    exact (mul_le_mul_of_nonneg_right
      (hf _ (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)).trans_eq
        (one_mul _)

theorem bounded_jackson_polynomial_exists
    (f : ℝ → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|)
    (K : ℕ) (hK : 0 < K) :
    ∃ P : Polynomial ℝ,
      P.natDegree ≤ 2 * (K - 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x - f x| ≤ 32 * L / (K : ℝ)) := by
  let f₁ : (Fin 1 → ℝ) → ℝ := fun z => f (z 0)
  have hf₁ : ContinuousOn f₁ (normalizedCube 1) :=
    (hf.comp (continuous_apply 0)).continuousOn
  obtain ⟨p, hpeval, hpdegree, _⟩ := tensorConvolution_exists_mvPolynomial hK f₁ hf₁
  let P : Polynomial ℝ := MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p
  have hEval (x : ℝ) : P.eval x = MvPolynomial.eval (fun _ : Fin 1 => x) p :=
    MvPolynomial.eval₂_const_uniqueAlgEquiv
  have hcos (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      cosPoint (fun _ : Fin 1 => Real.arccos x) = (fun _ : Fin 1 => x) := by
    funext i
    exact Real.cos_arccos hx.1 hx.2
  have hConv (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      P.eval x = tensorConvolution K f₁ (fun _ : Fin 1 => Real.arccos x) := by
    rw [hEval, ← hcos x hx]
    exact hpeval _
  refine ⟨P, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    apply MvPolynomial.notMem_support_iff.mp
    intro hmem
    have := hpdegree (Finsupp.single default n) hmem (0 : Fin 1)
    simp only [Fin.default_eq_zero, Finsupp.single_eq_same] at this
    omega
  · intro x hx
    rw [hConv x hx]
    apply tensorJackson_unit_bound hK
    intro z hz
    exact hbound (z 0) (hz 0)
  · intro x hx
    rw [hConv x hx]
    have h := tensorConvolution_approx_lipschitz hK f₁ L hL hf₁
      (fun z hz w hw => ?_) (fun _ : Fin 1 => Real.arccos x)
    · simpa only [hcos x hx, f₁, Nat.cast_one, mul_one] using h
    · simpa only [Fin.sum_univ_one, f₁] using hlip (z 0) (hz 0) (w 0) (hw 0)

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
