/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceAnalyticSeries
import Qatlib.Concepts.GradientOracle.GradientAlgo.AnalyticCentralDifferenceGridErrorStat
import Mathlib.Analysis.Analytic.Linear

/-!
# Coordinate tensors and analytic ray expansions

This module expands multilinear forms in the standard Euclidean basis and bounds diagonal
evaluation by coordinate coefficients. It then obtains a Taylor expansion along each ray under
the derivative growth condition used in [GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_tensor_growth`: coordinate bounds control diagonal evaluation by a power of the
  coordinate absolute sum.
* `centralDiff_ray_hasSum`: the ray Taylor series sums to `f (t • y)`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators Topology NNReal ENNReal

/-- Expands diagonal evaluation of a continuous multilinear form as a sum of standard-basis
coefficients times coordinate monomials. -/
theorem centralDiff_tensor_coordinates (d k : ℕ)
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    F (fun _ => y)=∑ α : Fin k → Fin d,
      F (fun i => EuclideanSpace.single (α i) (1 : ℝ))*(∏ i : Fin k,y (α i)) := by
  have hy : (∑ j : Fin d,y j • EuclideanSpace.single j (1 : ℝ))=y := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using!
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
  nth_rw 1 [← hy]
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [F.map_smul_univ,smul_eq_mul,mul_comm]

/-- If every standard-basis coefficient of a degree-`k` multilinear form has absolute value at
most `D`, its diagonal evaluation at `y` has absolute value at most `D*(∑ j, |y j|)^k`. -/
theorem centralDiff_tensor_growth (d k : ℕ)
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ)
    (D : ℝ)
    (hF : ∀ α : Fin k → Fin d,|F (fun i => EuclideanSpace.single (α i) (1 : ℝ))|≤D)
    (y : EuclideanSpace ℝ (Fin d)) :
    |F (fun _ => y)|≤D*(∑ j : Fin d,|y j|)^k := by
  rw [centralDiff_tensor_coordinates]
  calc
    _ ≤ ∑ α : Fin k → Fin d,|F (fun i => EuclideanSpace.single (α i) (1 : ℝ))*(∏ i : Fin k,y (α i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : Fin k → Fin d,D*(∏ i : Fin k,|y (α i)|) := by
      apply Finset.sum_le_sum
      intro α _
      rw [abs_mul,Finset.abs_prod]
      exact mul_le_mul_of_nonneg_right (hF α) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum,← Fintype.prod_sum (fun (_ : Fin k) (j : Fin d) => |y j|)]
      simp

/-- For an analytic function with the stated coordinate-derivative growth, the Taylor series of
its restriction to the ray through `y` sums to `f (t • y)` for every real `t`. -/
theorem centralDiff_ray_hasSum (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : AnalyticOnNhd ℝ f Set.univ) (c : ℝ) (hc : 0≤c)
    (hb : ∀ (k : ℕ) (α : Fin k → Fin d),
      |iteratedFDeriv ℝ k f 0 (fun i => EuclideanSpace.single (α i) (1 : ℝ))|
        ≤c^k*(k : ℝ)^((k : ℝ)/2))
    (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasSum (fun k : ℕ => iteratedFDeriv ℝ k f 0 (fun _ : Fin k => y)
      /(Nat.factorial k : ℝ)*t^k) (f (t • y)) := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) := (ContinuousLinearMap.id ℝ ℝ).smulRight y
  let g : ℝ → ℝ := f ∘ L
  have hg : AnalyticOnNhd ℝ g Set.univ :=
      fun t _ => (hf (L t) (Set.mem_univ _)).comp (L.analyticAt t)
  have he (k : ℕ) : iteratedDeriv k g 0=iteratedFDeriv ℝ k f 0 (fun _ : Fin k => y) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_right (hf.contDiff (n := k)) 0 le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero]
    simp [L]
  let A := c*(∑ j : Fin d,|y j|)
  have hA : 0≤A := mul_nonneg hc (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hbound (k : ℕ) : |iteratedDeriv k g 0|≤A^k*(k : ℝ)^((k : ℝ)/2) := by
    rw [he]
    have h := centralDiff_tensor_growth d k (iteratedFDeriv ℝ k f 0)
      (c^k*(k : ℝ)^((k : ℝ)/2)) (hb k) y
    simpa only [A,mul_pow,mul_assoc,mul_comm,mul_left_comm] using! h
  simpa only [he] using! centralDiff_scalar_entire_hasSum g hg A hA hbound t
end Qatlib.Concepts.GradientOracle.GradientAlgo
