/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceTensorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Taylor series for central-difference stencils

This module defines the Taylor contribution of each degree to a central-difference stencil and
proves that the series sums to the stencil evaluation. Polynomial exactness isolates the
derivative, while a geometric majorant controls the tail, as needed for
[GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_stencil_prefix`: the terms below degree `2*m+1` sum to the derivative at zero.
* `centralDiff_stencil_geometric_error`: a degreewise bound `T^k` yields error at most
  `T^(2*m+1)/(1-T)`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- The degree-`k` Taylor contribution to the central-difference stencil, formed from the
diagonal iterated derivative divided by `k!` and the signed stencil moment. -/
def centralDiffStencilTerm (d m : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (k : ℕ) : ℝ :=
  iteratedFDeriv ℝ k f 0 (fun _ : Fin k => y)/(Nat.factorial k : ℝ)*
    (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*(l : ℝ)^k)

/-- For an analytic function with the stated coordinate-derivative growth, the stencil-term
series sums to `centralDiffApply m f y`. -/
theorem centralDiff_stencil_hasSum (d m : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : AnalyticOnNhd ℝ f Set.univ) (c : ℝ) (hc : 0≤c)
    (hb : ∀ (k : ℕ) (α : Fin k → Fin d),
      |iteratedFDeriv ℝ k f 0 (fun i => EuclideanSpace.single (α i) (1 : ℝ))|
        ≤c^k*(k : ℝ)^((k : ℝ)/2)) (y : EuclideanSpace ℝ (Fin d)) :
    HasSum (centralDiffStencilTerm d m f y) (centralDiffApply m f y) := by
  have h := hasSum_sum (s := Finset.Ico (-(m : ℤ)) ((m : ℤ)+1))
    (fun l _ => (centralDiff_ray_hasSum d f hf c hc hb y (l : ℝ)).mul_left (centralDiffCoeff m l))
  convert! h using 1
  ext k
  dsimp [centralDiffStencilTerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- For positive stencil order `m`, the stencil-series terms of degrees below `2*m+1` sum
exactly to the derivative of `f` at zero applied to `y`. -/
theorem centralDiff_stencil_prefix (d m : ℕ) (hm : 0<m)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    (∑ k∈Finset.range (2*m+1),centralDiffStencilTerm d m f y k)=(fderiv ℝ f 0) y := by
  have hlow (k : ℕ) (hk : k∈Finset.range (2*m+1)) :
      centralDiffStencilTerm d m f y k=
        if k=1 then (fderiv ℝ f 0) y else 0 := by
    dsimp [centralDiffStencilTerm]
    rw [centralDifferenceExactness m hm k (by have h := Finset.mem_range.mp hk; omega)]
    split_ifs with h
    · subst k
      simp [iteratedFDeriv_one_apply]
    · simp
  rw [Finset.sum_congr rfl hlow,Finset.sum_ite_eq']
  simp [Finset.mem_range,show 1<2*m+1 by omega]

/-- For an analytic function with the stated derivative growth, a tail bound
`|centralDiffStencilTerm ... k| ≤ T^k` with `0 ≤ T < 1` gives derivative error at most
`T^(2*m+1)/(1-T)`. -/
theorem centralDiff_stencil_geometric_error (d m : ℕ) (hm : 0<m)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (c : ℝ) (hc : 0≤c)
    (hb : ∀ (k : ℕ) (α : Fin k → Fin d),
      |iteratedFDeriv ℝ k f 0 (fun i => EuclideanSpace.single (α i) (1 : ℝ))|
        ≤c^k*(k : ℝ)^((k : ℝ)/2)) (y : EuclideanSpace ℝ (Fin d))
    (T : ℝ) (hT0 : 0≤T) (hT1 : T<1)
    (hgood : ∀ k : ℕ,2*m+1≤k → |centralDiffStencilTerm d m f y k|≤T^k) :
    |(fderiv ℝ f 0) y-centralDiffApply m f y|≤T^(2*m+1)/(1-T) := by
  let N := 2*m+1
  have hs := centralDiff_stencil_hasSum d m f hf c hc hb y
  have hp := centralDiff_stencil_prefix d m hm f y
  have ht := (hasSum_nat_add_iff' N).mpr hs
  rw [hp] at ht
  have hmajor : Summable (fun j : ℕ => T^(j+N)) :=
    (summable_nat_add_iff N).mpr (summable_geometric_of_lt_one hT0 hT1)
  have hnorm : Summable (fun j : ℕ => ‖centralDiffStencilTerm d m f y (j+N)‖) := by
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _ hmajor
    intro j
    simpa only [Real.norm_eq_abs] using! hgood (j+N) (by omega)
  have hbound := (norm_tsum_le_tsum_norm hnorm).trans
    (hnorm.tsum_le_tsum (fun j => by simpa only [Real.norm_eq_abs] using! hgood (j+N) (by omega)) hmajor)
  rw [ht.tsum_eq,Real.norm_eq_abs,abs_sub_comm] at hbound
  have hgeom : (∑' j : ℕ,T^(j+N))=T^N/(1-T) := by
    simp only [pow_add,tsum_mul_right,tsum_geometric_of_lt_one hT0 hT1,div_eq_mul_inv,mul_comm]
  simpa only [hgeom] using! hbound
end Qatlib.Concepts.GradientOracle.GradientAlgo
