/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace Qatlib.Foundations.CoherentCompute.ProjectedError

theorem projectionWrongPythagoras {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x : E) :
    ‖x - K.starProjection x‖ ^ 2 + ‖K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hc : Kᗮ.starProjection x = x - K.starProjection x := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (K.starProjection_add_starProjection_orthogonal x)
  have hh := K.norm_sq_eq_add_norm_sq_starProjection x
  rw [hc] at hh
  linarith

theorem successOnSubspace_to_wrongSquared {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (U : E →ₗᵢ[ℂ] E) (ε : ℝ)
    (hsuccess : ∀ x : E, x ∈ W → ‖x‖ = 1 →
      1 - ε ≤ ‖K.starProjection (U x)‖ ^ 2) :
    ∀ x : E, x ∈ W → ‖U x - K.starProjection (U x)‖ ^ 2 ≤ ε * ‖x‖ ^ 2 := by
  intro x hx
  by_cases hzero : x = 0
  · simp [hzero]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  let c : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  let y := c • x
  have hc : ‖c‖ = ‖x‖⁻¹ := by simp [c, Complex.norm_real]
  have hy : ‖y‖ = 1 := by rw [show y = c • x from rfl, norm_smul, hc, inv_mul_cancel₀ hn]
  have hyW : y ∈ W := W.smul_mem c hx
  have hs := hsuccess y hyW hy
  have hpyth := projectionWrongPythagoras K (U y)
  rw [U.norm_map, hy] at hpyth
  have hbad : ‖U y - K.starProjection (U y)‖ ^ 2 ≤ ε := by nlinarith
  have heq : U y - K.starProjection (U y) = c • (U x - K.starProjection (U x)) := by
    simp only [y, map_smul, smul_sub]
  rw [heq, norm_smul, hc, mul_pow] at hbad
  calc
    ‖U x - K.starProjection (U x)‖ ^ 2 =
        ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * ‖U x - K.starProjection (U x)‖ ^ 2) := by field_simp
    _ ≤ ‖x‖ ^ 2 * ε := mul_le_mul_of_nonneg_left hbad (sq_nonneg _)
    _ = ε * ‖x‖ ^ 2 := by ring

theorem tensorIdentitySquaredBound {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (A P : Matrix I I ℂ) (ε : ℝ)
    (hbase : ∀ x : I → ℂ,
      ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ I)‖ ^ 2 ≤
        ε * ‖(WithLp.toLp 2 (P *ᵥ x) : EuclideanSpace ℂ I)‖ ^ 2)
    (z : I × J → ℂ) :
    ‖(WithLp.toLp 2 ((A ⊗ₖ (1 : Matrix J J ℂ)) *ᵥ z) : EuclideanSpace ℂ (I × J))‖ ^ 2 ≤
      ε * ‖(WithLp.toLp 2 ((P ⊗ₖ (1 : Matrix J J ℂ)) *ᵥ z) : EuclideanSpace ℂ (I × J))‖ ^ 2 := by
  have hslice (B : Matrix I I ℂ) (i : I) (j : J) :
      ((B ⊗ₖ (1 : Matrix J J ℂ)) *ᵥ z) (i,j) = (B *ᵥ (fun a => z (a,j))) i := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [hslice]
  calc
    (∑ i, ∑ j, ‖(A *ᵥ (fun a => z (a,j))) i‖ ^ 2) =
        ∑ j, ∑ i, ‖(A *ᵥ (fun a => z (a,j))) i‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, ε * ∑ i, ‖(P *ᵥ (fun a => z (a,j))) i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp] using hbase (fun a => z (a,j))
    _ = ε * ∑ i, ∑ j, ‖(P *ᵥ (fun a => z (a,j))) i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

theorem actualProjectionComputationAncilla
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W K : Submodule ℂ (EuclideanSpace ℂ I))
    [W.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    (U : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ I) (ε : ℝ)
    (hsuccess : ∀ x : EuclideanSpace ℂ I, x ∈ W → ‖x‖ = 1 →
      1 - ε ≤ ‖K.starProjection (U x)‖ ^ 2) :
    let P : Matrix I I ℂ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)).symm W.starProjection
    let A : Matrix I I ℂ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)).symm
      ((U.toContinuousLinearMap - K.starProjection.comp U.toContinuousLinearMap).comp W.starProjection)
    ∀ z : I × J → ℂ,
      ‖(WithLp.toLp 2 ((A ⊗ₖ (1 : Matrix J J ℂ)) *ᵥ z) : EuclideanSpace ℂ (I × J))‖ ^ 2 ≤
        ε * ‖(WithLp.toLp 2 ((P ⊗ₖ (1 : Matrix J J ℂ)) *ᵥ z) : EuclideanSpace ℂ (I × J))‖ ^ 2 := by
  dsimp only
  apply tensorIdentitySquaredBound
  intro x
  rw [← Matrix.toEuclideanCLM_toLp, ← Matrix.toEuclideanCLM_toLp]
  simp only [StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  exact successOnSubspace_to_wrongSquared W K U ε hsuccess
    (W.starProjection (WithLp.toLp 2 x)) (W.starProjection_apply_mem _)

end Qatlib.Foundations.CoherentCompute.ProjectedError
