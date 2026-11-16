/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Defs
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section




/-!
# Square singular value decomposition, including zero singular values.

The spectral theorem for the positive operator T†T gives a complete right singular basis. Normalizing its nonzero images and completing orthonormal families yields a full left basis, with all zero coefficients retained. The resulting matrix expansion works without invertibility assumptions.
-/

open Matrix Module
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

section Bases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A family with diagonal Gram matrix is a real scalar multiple of a full
orthonormal basis, provided the index count is the ambient dimension.
Zero vectors are filled using actual orthonormal completion. -/
theorem exists_orthonormalBasis_scaled_of_gram
    (hcard : finrank ℂ E = Fintype.card ι) (g : ι → E) (s : ι → ℝ)
    (hgram : ∀ i j, inner ℂ (g i) (g j) =
      (s j : ℂ) ^ 2 * (if i = j then 1 else 0)) :
    ∃ u : OrthonormalBasis ι ℂ E, ∀ i, g i = (s i : ℂ) • u i := by
  classical
  let S : Set ι := {i | s i ≠ 0}
  let w : ι → E := fun i => (((s i)⁻¹ : ℝ) : ℂ) • g i
  have hw : Orthonormal ℂ (S.domRestrict w) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change inner ℂ ((((s i.val)⁻¹ : ℝ) : ℂ) • g i.val)
      ((((s j.val)⁻¹ : ℝ) : ℂ) • g j.val) = if i = j then 1 else 0
    rw [inner_smul_left, inner_smul_right, hgram]
    simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
    by_cases hij : i = j
    · subst j
      have hi : s i.val ≠ 0 := i.property
      have hiC : (s i.val : ℂ) ≠ 0 := by exact_mod_cast hi
      simp only [ite_true, mul_one]
      field_simp [hiC]
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp only [ite_eq_right hij, ite_eq_right hval, mul_zero]
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨u, fun i => ?_⟩
  by_cases hi : s i = 0
  · have hgi : g i = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp (by
      simpa only [hi, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
        ite_true, zero_mul] using hgram i i)
    simp only [hgi, hi, Complex.ofReal_zero, zero_smul]
  · have hiS : i ∈ S := hi
    rw [hu i hiS]
    change g i = (s i : ℂ) • ((((s i)⁻¹ : ℝ) : ℂ) • g i)
    have hiC : (s i : ℂ) ≠ 0 := by exact_mod_cast hi
    simp only [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hiC, one_smul]

/-- Every complex endomorphism has two complete orthonormal singular-vector
bases, with nonnegative real singular values and all zero slots retained. -/
theorem exists_orthonormal_singular_bases (T : E →ₗ[ℂ] E) :
    ∃ (u v : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
      (s : Fin (finrank ℂ E) → ℝ),
      (∀ i, 0 ≤ s i) ∧ ∀ i, T (v i) = (s i : ℂ) • u i := by
  classical
  let hP := T.isPositive_adjoint_comp_self
  let v := hP.isSymmetric.eigenvectorBasis (n := finrank ℂ E) rfl
  let s : Fin (finrank ℂ E) → ℝ :=
    fun i => Real.sqrt (hP.isSymmetric.eigenvalues rfl i)
  have hs2 (i : Fin (finrank ℂ E)) :
      (s i : ℂ) ^ 2 = (hP.isSymmetric.eigenvalues rfl i : ℂ) := by
    have h := Real.sq_sqrt (hP.nonneg_eigenvalues rfl i)
    change (Real.sqrt (hP.isSymmetric.eigenvalues rfl i) : ℂ) ^ 2 = _
    exact_mod_cast h
  have hg (i j : Fin (finrank ℂ E)) :
      inner ℂ (T (v i)) (T (v j)) = (s j : ℂ) ^ 2 * (if i = j then 1 else 0) := by
    rw [← LinearMap.adjoint_inner_right T]
    change inner ℂ (v i) ((LinearMap.adjoint T ∘ₗ T) (v j)) = _
    have hj : (LinearMap.adjoint T ∘ₗ T) (v j) =
        (hP.isSymmetric.eigenvalues rfl j : ℂ) • v j :=
      hP.isSymmetric.apply_eigenvectorBasis rfl j
    rw [hj, inner_smul_right, v.inner_eq_ite, hs2]
  obtain ⟨u, hu⟩ := exists_orthonormalBasis_scaled_of_gram
    (by simp only [Fintype.card_fin]) (fun i => T (v i)) s hg
  exact ⟨u, v, s, fun _ => Real.sqrt_nonneg _, hu⟩

omit [DecidableEq ι] in
/-- The same complete SVD bases with any index type of the correct cardinality. -/
theorem exists_orthonormal_singular_bases_indexed
    (hcard : finrank ℂ E = Fintype.card ι) (T : E →ₗ[ℂ] E) :
    ∃ (u v : OrthonormalBasis ι ℂ E) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ∀ i, T (v i) = (s i : ℂ) • u i := by
  classical
  obtain ⟨u, v, s, hs, hT⟩ := exists_orthonormal_singular_bases T
  let e : Fin (finrank ℂ E) ≃ ι :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)
  refine ⟨u.reindex e, v.reindex e, fun i => s (e.symm i), fun i => hs _, ?_⟩
  intro i
  simpa only [OrthonormalBasis.reindex_apply] using hT (e.symm i)

omit [FiniteDimensional ℂ E] [DecidableEq ι] in
/-- The full rank-one operator expansion obtained from the two bases. -/
theorem singular_bases_expansion (T : E →ₗ[ℂ] E)
    (u v : OrthonormalBasis ι ℂ E) (s : ι → ℝ)
    (hT : ∀ i, T (v i) = (s i : ℂ) • u i) (x : E) :
    T x = ∑ i, ((s i : ℂ) * inner ℂ (v i) x) • u i := by
  calc
    T x = T (∑ i, inner ℂ (v i) x • v i) :=
      congrArg T (v.sum_repr' x).symm
    _ = ∑ i, inner ℂ (v i) x • T (v i) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ i, ((s i : ℂ) * inner ℂ (v i) x) • u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hT, smul_smul, mul_comm]

end Bases

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Full square-matrix SVD on the original index space, not a doubled dilation. -/
theorem exists_square_svd (A : Matrix n n ℂ) :
    ∃ (U V : Matrix n n ℂ) (s : n → ℝ),
      U ∈ unitary (Matrix n n ℂ) ∧ V ∈ unitary (Matrix n n ℂ) ∧
      (∀ i, 0 ≤ s i) ∧ A = U * diagonal (fun i => (s i : ℂ)) * Vᴴ := by
  classical
  obtain ⟨u, v, s, hs, hT⟩ := exists_orthonormal_singular_bases_indexed
    (ι := n) (E := EuclideanSpace ℂ n) finrank_euclideanSpace A.toEuclideanLin
  let U : Matrix n n ℂ := fun i j => u j i
  let V : Matrix n n ℂ := fun i j => v j i
  have hU : U ∈ unitary (Matrix n n ℂ) := by
    change (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix u ∈ Matrix.unitaryGroup n ℂ
    exact (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary u
  have hV : V ∈ unitary (Matrix n n ℂ) := by
    change (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix v ∈ Matrix.unitaryGroup n ℂ
    exact (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary v
  have hAV : A * V = U * diagonal (fun i => (s i : ℂ)) := by
    ext i j
    have hij := congrArg (fun x : EuclideanSpace ℂ n => x i) (hT j)
    change (A *ᵥ fun k => v j k) i = (s j : ℂ) * u j i at hij
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    change (∑ k, A i k * v j k) = u j i * (s j : ℂ)
    exact hij.trans (mul_comm _ _)
  refine ⟨U, V, s, hU, hV, hs, ?_⟩
  have hV1 : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
  calc
    A = A * (V * Vᴴ) := by rw [hV1, Matrix.mul_one]
    _ = (A * V) * Vᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = U * diagonal (fun i => (s i : ℂ)) * Vᴴ := by rw [hAV]

end Matrices

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
