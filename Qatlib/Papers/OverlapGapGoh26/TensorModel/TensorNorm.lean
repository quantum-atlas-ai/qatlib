/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Multilinear tensor energy bounds

`tensorForm` realizes a finite tensor as a continuous multilinear form on Euclidean space.
Bounds on differences of multilinear forms yield energy and energy-density estimates supporting
the tensor analysis in [GohMuller2026].

## Main statements

* `tensorEnergy_eq_form`: tensor energy is the diagonal evaluation of the multilinear form.
* `actual_energy_density_difference`: the form norm controls changes in energy density.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm

/-- The continuous linear functional extracting coordinate `i` of a Euclidean vector. -/
def coordinate {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin N)→L[ℝ]ℝ :=
  innerSL ℝ (WithLp.toLp 2 (Pi.single i 1))

/-- The coordinate functional `coordinate i` evaluates a vector to its `i`th entry. -/
theorem coordinate_apply {N : ℕ} (i : Fin N) (x : EuclideanSpace ℝ (Fin N)) : coordinate i x=x i := by
  change inner ℝ (WithLp.toLp 2 (Pi.single i 1) : EuclideanSpace ℝ (Fin N)) x=x i
  simp [PiLp.inner_apply,RCLike.inner_apply]

/-- The continuous multilinear monomial taking the product of the coordinates selected by `k`,
one from each argument. -/
def monomial {q N : ℕ} (k : Fin q→Fin N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => EuclideanSpace ℝ (Fin N)) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ).compContinuousLinearMap (fun a => coordinate (k a))

/-- The continuous multilinear form obtained by summing the coordinate monomials with
coefficients from `A`. -/
def tensorForm {q N : ℕ} (A : Tensor q N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => EuclideanSpace ℝ (Fin N)) ℝ :=
  ∑ k,A k•monomial k

/-- The multilinear form of `A` evaluates to the sum of its coefficients times the corresponding
coordinate products. -/
theorem tensorForm_apply {q N : ℕ} (A : Tensor q N) (z : Fin q→EuclideanSpace ℝ (Fin N)) :
    tensorForm A z=∑ k,A k*∏ a,z a (k a) := by
  simp [tensorForm,monomial,ContinuousMultilinearMap.sum_apply,ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,ContinuousMultilinearMap.mkPiAlgebra_apply,coordinate_apply]

/-- The tensor energy of a Euclidean vector equals the diagonal evaluation of `tensorForm`. -/
theorem tensorEnergy_eq_form {q N : ℕ} (A : Tensor q N) (x : EuclideanSpace ℝ (Fin N)) :
    tensorEnergy A (WithLp.ofLp x)=tensorForm A (fun _ : Fin q => x) := by
  rw [tensorForm_apply]
  rfl

/-- The difference of two evaluations of `tensorForm` is bounded by its norm times the arity,
the maximal argument norm to the preceding power, and the argument distance. -/
theorem actual_multilinear_difference {q N : ℕ} (A : Tensor q N)
    (u v : Fin q→EuclideanSpace ℝ (Fin N)) :
    |tensorForm A u-tensorForm A v|≤
      ‖tensorForm A‖*(q:ℝ)*max ‖u‖ ‖v‖^(q-1)*‖u-v‖ := by
  simpa only [Real.norm_eq_abs,Fintype.card_fin] using (tensorForm A).norm_image_sub_le u v

/-- For an order-`r + 1` tensor, the energy difference is bounded by its form norm times `r +
1`, the maximal vector norm to power `r`, and the vector distance. -/
theorem actual_energy_difference {r N : ℕ} (A : Tensor (r+1) N) (x y : EuclideanSpace ℝ (Fin N)) :
    |tensorEnergy A (WithLp.ofLp x)-tensorEnergy A (WithLp.ofLp y)|≤
      ‖tensorForm A‖*((r+1:ℕ):ℝ)*max ‖x‖ ‖y‖^r*‖x-y‖ := by
  have h := actual_multilinear_difference A (fun _ => x) (fun _ => y)
  have hd : (fun _ : Fin (r+1) => x)-(fun _ => y)=(fun _ => x-y) := rfl
  rw [hd] at h
  simpa only [← tensorEnergy_eq_form,pi_norm_const,Nat.add_sub_cancel] using h

/-- For positive `N`, division by `N` gives the corresponding multilinear-form bound on the
difference of energy densities. See [GohMuller2026]. -/
theorem actual_energy_density_difference {r N : ℕ} (hN : 0<N)
    (A : Tensor (r+1) N) (x y : EuclideanSpace ℝ (Fin N)) :
    |tensorEnergy A (WithLp.ofLp x)/(N:ℝ)-tensorEnergy A (WithLp.ofLp y)/(N:ℝ)|≤
      (‖tensorForm A‖*((r+1:ℕ):ℝ)*max ‖x‖ ‖y‖^r/(N:ℝ))*‖x-y‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [← sub_div,abs_div,abs_of_pos hn]
  exact (div_le_div_of_nonneg_right (actual_energy_difference A x y) hn.le).trans_eq (by ring)

end Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
