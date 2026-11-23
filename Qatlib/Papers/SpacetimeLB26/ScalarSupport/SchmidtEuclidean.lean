/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# A Euclidean Schmidt-rank overlap bound

This module proves a pure-state row-support case of [BhartiHaugTanggara2026], Lemma 4.
A bipartite pure state is represented by its coefficients in
`EuclideanSpace ℂ (Fin D × Fin D)`. Confining the left-factor rows to `d` coordinates
in the fixed basis bounds the Schmidt rank by `d`. The maximally entangled vector is
the normalized diagonal vector.

The overlap is the squared Euclidean inner product with that vector.  The proof is the
usual Cauchy–Schwarz estimate on the supported diagonal coefficients. The general pure-state
rank condition and the convex extension to mixed states are outside this model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.SchmidtEuclidean

open scoped BigOperators InnerProductSpace

/-- The unnormalized diagonal vector in the native bipartite coefficient basis. -/
def diagonalUnit (D : ℕ) : EuclideanSpace ℂ (Fin D × Fin D) :=
  WithLp.toLp 2 fun p : Fin D × Fin D => if p.1 = p.2 then 1 else 0

/-- The normalized maximally entangled vector on `Fin D × Fin D`. -/
def maxEntangled (D : ℕ) : EuclideanSpace ℂ (Fin D × Fin D) :=
  ((Real.sqrt D : ℝ)⁻¹ : ℂ) • diagonalUnit D

/-- Squared inner product with `maxEntangled D`, i.e. the overlap used in Lemma 4. -/
def maxEntangledOverlap (D : ℕ) (ψ : EuclideanSpace ℂ (Fin D × Fin D)) : ℝ :=
  ‖⟪maxEntangled D, ψ⟫_ℂ‖ ^ 2

/--
If a normalized Euclidean coefficient vector has all left-factor rows in a support of
size `d`, then its overlap with the normalized maximally entangled vector is at most
`d / D`. The dimension is positive, and normalization excludes empty support.
-/
theorem schmidt_rank_overlap_bound
    {D d : ℕ} (hD : 0 < D) (R : Finset (Fin D)) (hRcard : R.card = d)
    (ψ : EuclideanSpace ℂ (Fin D × Fin D)) (hψ : ‖ψ‖ = 1)
    (hsupport : ∀ p : Fin D × Fin D, p.1 ∉ R → ψ p = 0) :
    maxEntangledOverlap D ψ ≤ (d : ℝ) / (D : ℝ) := by
  have hψsq : ‖ψ‖ ^ 2 = 1 := by
    rw [hψ]
    norm_num
  have hψcoeff : ∑ p : Fin D × Fin D, ‖ψ p‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    exact hψsq
  set trace : ℂ := ∑ i : Fin D, ψ (i, i) with htrace
  have htraceR : trace = ∑ i ∈ R, ψ (i, i) := by
    rw [htrace]
    exact (Finset.sum_subset (Finset.subset_univ R) fun i _ hi =>
      hsupport (i, i) hi).symm
  have hdiagle : ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2 ≤ 1 := by
    calc ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2
        ≤ ∑ i : Fin D, ‖ψ (i, i)‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
            fun _ _ _ => pow_nonneg (norm_nonneg _) 2
      _ ≤ ∑ i : Fin D, ∑ j : Fin D, ‖ψ (i, j)‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.single_le_sum (f := fun j => ‖ψ (i, j)‖ ^ 2)
              (fun _ _ => pow_nonneg (norm_nonneg _) 2) (Finset.mem_univ i)
      _ = ∑ p : Fin D × Fin D, ‖ψ p‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
      _ = 1 := hψcoeff
  have htri : ‖∑ i ∈ R, ψ (i, i)‖ ≤ ∑ i ∈ R, ‖ψ (i, i)‖ :=
    norm_sum_le R _
  have htriNonneg : 0 ≤ ∑ i ∈ R, ‖ψ (i, i)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1 : ℝ))
    (fun i => ‖ψ (i, i)‖)
  have htraceSq : ‖trace‖ ^ 2 ≤ (d : ℝ) * ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2 := by
    have h1 : ‖trace‖ ≤ ∑ i ∈ R, ‖ψ (i, i)‖ := by
      rw [htraceR]
      exact htri
    have h2 : ‖trace‖ ^ 2 ≤ (∑ i ∈ R, ‖ψ (i, i)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) htriNonneg).2 h1
    calc ‖trace‖ ^ 2 ≤ (∑ i ∈ R, ‖ψ (i, i)‖) ^ 2 := h2
      _ = (∑ i ∈ R, (1 : ℝ) * ‖ψ (i, i)‖) ^ 2 := by simp
      _ ≤ (∑ i ∈ R, (1 : ℝ) ^ 2) * ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2 := hcs
      _ = (d : ℝ) * ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2 := by simp [hRcard]
  have hinnerdiag : ⟪diagonalUnit D, ψ⟫_ℂ = trace := by
    simp [diagonalUnit, htrace, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fintype.sum_prod_type]
  have hinner : ‖⟪maxEntangled D, ψ⟫_ℂ‖ = ((Real.sqrt D : ℝ)⁻¹ : ℝ) * ‖trace‖ := by
    rw [maxEntangled, inner_smul_left, hinnerdiag, norm_mul]
    congr 1
    simp [Complex.conj_ofReal]
  unfold maxEntangledOverlap
  rw [hinner]
  have hinvsq : (((Real.sqrt D : ℝ)⁻¹ : ℝ) * ‖trace‖) ^ 2 =
      ((Real.sqrt D : ℝ) ^ 2)⁻¹ * ‖trace‖ ^ 2 := by
    rw [mul_pow, inv_pow]
  have hDinv_nonneg : 0 ≤ ((D : ℝ))⁻¹ := by positivity
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  rw [hinvsq, Real.sq_sqrt (by exact_mod_cast hD.le)]
  calc ((D : ℝ))⁻¹ * ‖trace‖ ^ 2
      ≤ ((D : ℝ))⁻¹ * ((d : ℝ) * ∑ i ∈ R, ‖ψ (i, i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htraceSq hDinv_nonneg
    _ ≤ ((D : ℝ))⁻¹ * (d : ℝ) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hdiagle, hd_nonneg]) hDinv_nonneg
    _ = (d : ℝ) / (D : ℝ) := by field_simp

/-- The constant in the uniform finite-dimensional Schmidt overlap bound is outside all
dimension and rank quantifiers. -/
theorem schmidt_rank_overlap_uniform_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D d : ℕ) (_ : 0 < D) (R : Finset (Fin D)) (_ : R.card = d)
        (ψ : EuclideanSpace ℂ (Fin D × Fin D)) (_ : ‖ψ‖ = 1)
        (_ : ∀ p : Fin D × Fin D, p.1 ∉ R → ψ p = 0),
        maxEntangledOverlap D ψ ≤ C * ((d : ℝ) / (D : ℝ)) := by
  refine ⟨1, one_pos, fun D d hD R hRcard ψ hψ hsupport => ?_⟩
  have := schmidt_rank_overlap_bound hD R hRcard ψ hψ hsupport
  simpa using this

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.SchmidtEuclidean
