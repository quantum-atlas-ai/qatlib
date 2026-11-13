/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan, Qatlib Contributors
Adapted from https://github.com/Jiyuan-Tan/CausalSmith@47acf19
-/

import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Lagrange

/-!
# Tensor Jackson kernels

This module defines the product Jackson kernel `tensorJackson` on `periodBox` and its
convolution with a function composed with the coordinatewise cosine map `cosPoint`. It proves
normalization, coordinate moment identities, preservation of nonnegativity, and preservation of
constants. These constructions support the polynomial approximation methods used in
[WangEtAl2026].

## Main statements

* `tensorJackson_integral_eq_one`: the product kernel has integral one for positive order.
* `tensorJackson_first_moment_eq`: each coordinate first absolute moment reduces to a
  one-dimensional moment.
* `tensorConvolution_const`: convolution preserves constant functions.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Approximation

section

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators

/-- The box of vectors whose coordinates lie in `[-π, π]`. -/
def periodBox (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-Real.pi) Real.pi}

/-- The cube of vectors whose coordinates lie in `[-1, 1]`. -/
def normalizedCube (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- The product of the one-dimensional Jackson kernels of order `K` over all `d` coordinates. -/
noncomputable def tensorJackson (K d : ℕ) (u : Fin d → ℝ) : ℝ :=
  ∏ i, jackson K (u i)

/-- The coordinatewise cosine map from real vectors to the normalized cube. -/
noncomputable def cosPoint {d : ℕ} (t : Fin d → ℝ) : Fin d → ℝ := fun i => Real.cos (t i)

/-- The coordinatewise cosine of every real vector lies in `normalizedCube`. -/
theorem cosPoint_mem_normalizedCube {d : ℕ} (t : Fin d → ℝ) :
    cosPoint t ∈ normalizedCube d := by
  intro i
  exact ⟨Real.neg_one_le_cos (t i), Real.cos_le_one (t i)⟩

/-- The integral of `f` composed with the shifted coordinatewise cosine map against the product
Jackson kernel on `periodBox`. -/
noncomputable def tensorConvolution {d : ℕ} (K : ℕ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u

/-- The product Jackson kernel is nonnegative when `K` is positive. -/
theorem tensorJackson_nonneg {d K : ℕ} (hK : 0 < K) (u : Fin d → ℝ) :
    0 ≤ tensorJackson K d u := by
  exact Finset.prod_nonneg fun i _ ↦ jackson_nonneg K hK (u i)

/-- The product Jackson kernel is measurable for every order and dimension. -/
@[fun_prop]
theorem measurable_tensorJackson (K d : ℕ) : Measurable (tensorJackson K d) := by
  unfold tensorJackson
  fun_prop

/-- The product Jackson kernel is integrable on `periodBox`. -/
theorem integrableOn_tensorJackson (K d : ℕ) :
    IntegrableOn (tensorJackson K d) (periodBox d) := by
  change Integrable (fun u : Fin d → ℝ ↦ ∏ i, jackson K (u i))
    (volume.restrict (periodBox d))
  rw [show periodBox d = Set.univ.pi (fun _ ↦ Set.Icc (-Real.pi) Real.pi) by
    ext u
    simp only [periodBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc], volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun _ ↦ integrableOn_jackson K

/-- Integration of a product of coordinate functions over `periodBox` factors into the product
of their one-dimensional integrals. -/
theorem integral_periodBox_prod {d : ℕ} (g : Fin d → ℝ → ℝ) :
    (∫ u in periodBox d, ∏ i, g i (u i)) =
      ∏ i, ∫ t in Set.Icc (-Real.pi) Real.pi, g i t := by
  rw [show periodBox d = Set.univ.pi (fun _ ↦ Set.Icc (-Real.pi) Real.pi) by
    ext u
    simp only [periodBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc], volume_pi, Measure.restrict_pi_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod g

/-- For positive `K`, the integral of `tensorJackson K d` over `periodBox d` is one. -/
theorem tensorJackson_integral_eq_one {d K : ℕ} (hK : 0 < K) :
    (∫ u in periodBox d, tensorJackson K d u) = 1 := by
  rw [show tensorJackson K d = fun u ↦ ∏ i, jackson K (u i) by rfl,
    integral_periodBox_prod (fun _ ↦ jackson K)]
  simp [jackson_integral_eq_one K hK]

/-- Each coordinate first absolute moment of the product Jackson kernel equals the corresponding
one-dimensional Jackson moment. -/
theorem tensorJackson_first_moment_eq {d K : ℕ} (hK : 0 < K) (i : Fin d) :
    (∫ u in periodBox d, |u i| * tensorJackson K d u) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t := by
  classical
  let g : Fin d → ℝ → ℝ := fun j t ↦ (if j = i then |t| else 1) * jackson K t
  have hi : IntegrableOn (fun t : ℝ ↦ |t| * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    ((continuous_abs.comp continuous_id).mul (continuous_jackson K)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hg : ∀ j, IntegrableOn (g j) (Set.Icc (-Real.pi) Real.pi) := by
    intro j
    by_cases hji : j = i
    · simpa [g, hji] using hi
    · simpa [g, hji] using integrableOn_jackson K
  rw [show (fun u : Fin d → ℝ ↦ |u i| * tensorJackson K d u) =
      fun u ↦ ∏ j, g j (u j) by
    funext u
    symm
    calc
      (∏ j, g j (u j)) =
          (∏ j, if j = i then |u j| else 1) * ∏ j, jackson K (u j) := by
        simp only [g, Finset.prod_mul_distrib]
      _ = |u i| * tensorJackson K d u := by simp [tensorJackson],
    integral_periodBox_prod g]
  have hmass : (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) = 1 :=
    jackson_integral_eq_one K hK
  have hcoord : ∀ j, (∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
      if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t) else 1 := by
    intro j
    by_cases hji : j = i <;> simp [g, hji, hmass]
  calc
    (∏ j, ∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
        ∏ j, if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t)
          else 1 := Finset.prod_congr rfl fun j _ ↦ hcoord j
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t := by simp

/-- Each coordinate second moment of the product Jackson kernel equals the one-dimensional
Jackson second moment. -/
theorem tensorJackson_second_moment_eq {d K : ℕ} (hK : 0 < K) (i : Fin d) :
    (∫ u in periodBox d, (u i) ^ 2 * tensorJackson K d u) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t := by
  classical
  let g : Fin d → ℝ → ℝ := fun j t ↦ (if j = i then t ^ 2 else 1) * jackson K t
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ 2 * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    ((continuous_id.pow 2).mul (continuous_jackson K)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hg : ∀ j, IntegrableOn (g j) (Set.Icc (-Real.pi) Real.pi) := by
    intro j
    by_cases hji : j = i
    · simpa [g, hji] using hi
    · simpa [g, hji] using integrableOn_jackson K
  rw [show (fun u : Fin d → ℝ ↦ (u i) ^ 2 * tensorJackson K d u) =
      fun u ↦ ∏ j, g j (u j) by
    funext u
    symm
    calc
      (∏ j, g j (u j)) =
          (∏ j, if j = i then (u j) ^ 2 else 1) * ∏ j, jackson K (u j) := by
        simp only [g, Finset.prod_mul_distrib]
      _ = (u i) ^ 2 * tensorJackson K d u := by simp [tensorJackson],
    integral_periodBox_prod g]
  have hmass : (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) = 1 :=
    jackson_integral_eq_one K hK
  have hcoord : ∀ j, (∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
      if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) else 1 := by
    intro j
    by_cases hji : j = i <;> simp [g, hji, hmass]
  calc
    (∏ j, ∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
        ∏ j, if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t)
          else 1 := Finset.prod_congr rfl fun j _ ↦ hcoord j
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t := by simp

/-- For positive `K`, tensor Jackson convolution is nonnegative whenever `f` is nonnegative on
the normalized cube. -/
theorem tensorConvolution_nonneg {d K : ℕ} (hK : 0 < K)
    {f : (Fin d → ℝ) → ℝ} (hf : ∀ z ∈ normalizedCube d, 0 ≤ f z) (x : Fin d → ℝ) :
    0 ≤ tensorConvolution K f x := by
  rw [tensorConvolution]
  exact integral_nonneg fun u ↦
    mul_nonneg (hf _ (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)

/-- For positive `K`, tensor Jackson convolution preserves constant functions. -/
theorem tensorConvolution_const {d K : ℕ} (hK : 0 < K) (c : ℝ) (x : Fin d → ℝ) :
    tensorConvolution K (fun _ => c) x = c := by
  unfold tensorConvolution
  rw [integral_const_mul, tensorJackson_integral_eq_one hK, mul_one]

end Causalean.Mathlib.Analysis.JacksonApproximation

end
end Qatlib.Foundations.CbmdAnalysis.Approximation
