/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceGridTerms
import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceExceptionalUnion

/-!
# Analytic central-difference error on a grid

This module proves `analyticCentralDifferenceGridError` by combining tensor concentration,
stencil-series bounds, and a union estimate over high degrees. The result supplies a finite-grid
analytic approximation guarantee for the gradient methods associated with
[GilyenArunachalamWiebe2019].

## Main statements

* `analyticCentralDifferenceGridError`: at most a `1/1000` fraction of grid points exceed the
  specified geometric error threshold.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- For analytic functions with the specified coordinate-derivative growth, proves that at most
`M^d/1000` grid points exceed the geometric central-difference error threshold when
`8*R*c*m*sqrt d < 1`. See [GilyenArunachalamWiebe2019]. -/
theorem analyticCentralDifferenceGridError : AnalyticCentralDifferenceGridError := by
  intro d m hm R c hR hc f hf hb M hconv
  by_cases hd : d=0
  · subst d
    have hpoint (z : Fin 0 → Fin M) : gridPoint 0 M R z=0 := Subsingleton.elim _ _
    have hcoeff : (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l)=0 := by
      simpa only [pow_zero,mul_one,if_neg (by norm_num : (0 : ℕ)≠1)] using!
          centralDifferenceExactness m hm 0 (by omega)
    have hstencil : centralDiffApply m f (0 : EuclideanSpace ℝ (Fin 0))=0 := by
      dsimp [centralDiffApply]
      simp only [smul_zero,← Finset.sum_mul,hcoeff,zero_mul]
    simp only [hpoint,hstencil,Finset.univ_eq_empty,Finset.sum_empty,sub_self,abs_zero,
      Real.sqrt_zero,mul_zero,zero_pow (by omega : 2*m+1≠0),zero_div,lt_self_iff_false,
      Finset.filter_false,Finset.card_empty,Nat.cast_zero,pow_zero,Nat.cast_one]
    norm_num
  have hd0 : 0<d := Nat.pos_of_ne_zero hd
  let N := 2*m+1
  let T := 8*R*c*m*Real.sqrt d
  let H := fun (k : ℕ) (α : Fin k → Fin d) =>
    iteratedFDeriv ℝ k f 0 (fun i => EuclideanSpace.single (α i) (1 : ℝ)) /
      (c^k*(k : ℝ)^((k : ℝ)/2))
  let B := fun (k : ℕ) (z : Fin d → Fin M) =>
    Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k≤
      |∑ α : Fin k → Fin d,H k α*(∏ i : Fin k,gridCenter M 1 (z (α i)))|
  let E := fun z : Fin d → Fin M => T^N/(1-T)<
    |(fderiv ℝ f 0) (gridPoint d M R z)-centralDiffApply m f (gridPoint d M R z)|
  have hcount (k : ℕ) (hk : N≤k) :
      ((Finset.univ.filter (B k)).card : ℝ)≤((M^d : ℕ) : ℝ)*(1/16 : ℝ)^k := by
    have hk0 : 0<k := by dsimp [N] at hk; omega
    have hkR : (0 : ℝ)<k := by exact_mod_cast hk0
    have hD : 0<c^k*(k : ℝ)^((k : ℝ)/2) := mul_pos (pow_pos hc _) (Real.rpow_pos_of_pos hkR _)
    have hH (α : Fin k → Fin d) : |H k α|≤1 := by
      dsimp [H]
      rw [abs_div,abs_of_nonneg hD.le]
      exact (div_le_one hD).mpr (hb k α)
    have h := centralDiff_grid_tensor_count d k M hd0 hk0 4 (by norm_num) (H k) hH
    have hpow : (4 : ℝ)^(2*k)=16^k := by rw [pow_mul]; norm_num
    change _≤_ at h
    simpa only [B,hpow,div_eq_mul_inv,inv_pow,one_mul] using! h
  have hcover (z : Fin d → Fin M) (hz : E z) : ∃ k,N≤k ∧ B k z := by
    by_contra h
    push Not at h
    have hgood (k : ℕ) (hk : 2*m+1≤k) :
        |centralDiffStencilTerm d m f (gridPoint d M R z) k|≤T^k := by
      apply centralDiff_grid_good_term d m k M hd0 hm hk R c hR hc f z
      exact (lt_of_not_ge (h k hk)).le
    have herror := centralDiff_stencil_geometric_error d m hm f hf c hc.le hb
      (gridPoint d M R z) T (by positivity) hconv hgood
    exact (not_lt_of_ge herror) hz
  have htotal := centralDiff_exceptional_union E B N (by dsimp [N]; omega)
    (((M^d : ℕ) : ℝ)) (Nat.cast_nonneg _) hcount hcover
  simp_rw [centralDiff_grid_first]
  exact htotal
end Qatlib.Concepts.GradientOracle.GradientAlgo
