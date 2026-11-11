/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceGridConstants
import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceGridGeometry
import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceStencilSeries

/-!
# Central-difference terms on centered grids

This module expresses multilinear evaluations at grid points through coordinate tensors and
identifies the first-order contribution. It converts a normalized tensor bound into a geometric
stencil-term bound, supporting [GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_grid_tensor_identity`: coordinate expansion with scale and normalization factors.
* `centralDiff_grid_good_term`: the stated tensor threshold bounds the stencil term by
  `(8*R*c*m*sqrt d)^k`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- For nonzero normalization `D`, expands a multilinear form on a grid vector as `D*R^k` times
the normalized coordinate-tensor polynomial on the unit grid. -/
theorem centralDiff_grid_tensor_identity (d k M : ℕ) (R D : ℝ) (hD : D≠0)
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ)
    (z : Fin d → Fin M) :
    F (fun _ => gridPoint d M R z)=D*R^k*
      (∑ α : Fin k → Fin d,(F (fun i => EuclideanSpace.single (α i) (1 : ℝ))/D)*
        (∏ i : Fin k,gridCenter M 1 (z (α i)))) := by
  have hcoord (j : Fin d) : (gridPoint d M R z) j=R*gridCenter M 1 (z j) := by
    dsimp [gridPoint,gridCenter]
    ring
  rw [centralDiff_tensor_coordinates,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  field_simp

/-- The coordinate sum of first derivatives weighted by grid centers equals the derivative at
zero applied to the grid vector. -/
theorem centralDiff_grid_first (d M : ℕ) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (z : Fin d → Fin M) :
    (∑ j : Fin d,(fderiv ℝ f 0) (EuclideanSpace.single j (1 : ℝ))*gridCenter M R (z j))=
      (fderiv ℝ f 0) (gridPoint d M R z) := by
  have hy : (∑ j : Fin d,gridCenter M R (z j) • EuclideanSpace.single j (1 : ℝ))=gridPoint d M R z := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using!
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (gridPoint d M R z)
  rw [← hy,map_sum]
  simp only [map_smul,smul_eq_mul,mul_comm]

/-- Under the stated degree, positivity, and normalized tensor bound, the absolute
stencil-series term at a grid point is at most `(8*R*c*m*sqrt d)^k`. -/
theorem centralDiff_grid_good_term (d m k M : ℕ) (hd : 0<d) (hm : 0<m)
    (hk : 2*m+1≤k) (R c : ℝ) (hR : 0<R) (hc : 0<c)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (z : Fin d → Fin M)
    (hgood : |∑ α : Fin k → Fin d,
      (iteratedFDeriv ℝ k f 0 (fun i => EuclideanSpace.single (α i) (1 : ℝ)) /
        (c^k*(k : ℝ)^((k : ℝ)/2)))*
        (∏ i : Fin k,gridCenter M 1 (z (α i)))|
      ≤Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k) :
    |centralDiffStencilTerm d m f (gridPoint d M R z) k|≤(8*R*c*m*Real.sqrt d)^k := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  let D := c^k*(k : ℝ)^((k : ℝ)/2)
  have hD : 0<D := mul_pos (pow_pos hc _) (Real.rpow_pos_of_pos hkR _)
  have hF : |iteratedFDeriv ℝ k f 0 (fun _ : Fin k => gridPoint d M R z)|≤
      D*R^k*(Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k) := by
    rw [centralDiff_grid_tensor_identity d k M R D hD.ne',abs_mul,
      abs_of_nonneg (mul_nonneg hD.le (pow_nonneg hR.le k))]
    exact mul_le_mul_of_nonneg_left hgood (mul_nonneg hD.le (pow_nonneg hR.le k))
  have hmoment := centralDiff_signed_moment_bound m k hm hk
  have hnum : |centralDiffStencilTerm d m f (gridPoint d M R z) k|≤
      (D*R^k*(Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k))/(Nat.factorial k : ℝ)*
        (6*Real.exp (-(7/6 : ℝ)*m)*(m : ℝ)^k*Real.sqrt m) := by
    dsimp [centralDiffStencilTerm]
    rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg (Nat.factorial k) : (0 : ℝ)≤Nat.factorial k)]
    exact mul_le_mul (div_le_div_of_nonneg_right hF (Nat.cast_nonneg _)) hmoment (abs_nonneg _)
        (by positivity)
  apply hnum.trans
  simpa only [D,mul_assoc,mul_comm,mul_left_comm,div_eq_mul_inv] using!
    centralDiff_grid_degree_constant d m k hd hm hk R c hR hc
end Qatlib.Concepts.GradientOracle.GradientAlgo
