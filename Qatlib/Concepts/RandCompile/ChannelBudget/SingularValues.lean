/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
import Mathlib.Analysis.InnerProductSpace.SingularValues
set_option warningAsError false

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix Module
open scoped ComplexConjugate

section SingularValueBridge

variable {I O : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype O]

noncomputable def matrixSingularValues (A : Matrix O I ℂ) : ℕ →₀ ℝ :=
  A.toEuclideanLin.singularValues

@[simp]
theorem matrixSingularValues_apply (A : Matrix O I ℂ) (i : ℕ) :
    matrixSingularValues A i = A.toEuclideanLin.singularValues i := rfl

theorem matrixSingularValues_nonneg (A : Matrix O I ℂ) (i : ℕ) :
    0 ≤ matrixSingularValues A i :=
  A.toEuclideanLin.singularValues_nonneg i

theorem matrixSingularValues_of_card_le (A : Matrix O I ℂ) {i : ℕ}
    (hi : Fintype.card I ≤ i) : matrixSingularValues A i = 0 := by
  apply A.toEuclideanLin.singularValues_of_finrank_le
  simpa using hi

@[simp]
theorem support_matrixSingularValues (A : Matrix O I ℂ) :
    (matrixSingularValues A).support =
      Finset.range (finrank ℂ A.toEuclideanLin.range) :=
  A.toEuclideanLin.support_singularValues

theorem matrixSingularValues_pos_iff_lt_finrank_range (A : Matrix O I ℂ) {i : ℕ} :
    0 < matrixSingularValues A i ↔ i < finrank ℂ A.toEuclideanLin.range :=
  A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range

noncomputable def rightSingularBasis (A : Matrix O I ℂ) :
    OrthonormalBasis (Fin (Fintype.card I)) ℂ (EuclideanSpace ℂ I) :=
  A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace

@[simp]
theorem norm_rightSingularBasis (A : Matrix O I ℂ) (i : Fin (Fintype.card I)) :
    ‖rightSingularBasis A i‖ = 1 :=
  (rightSingularBasis A).norm_eq_one i

theorem adjoint_comp_apply_rightSingularBasis (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (rightSingularBasis A i) =
      ((matrixSingularValues A i : ℂ) ^ 2) • rightSingularBasis A i := by
  have h :=
    A.toEuclideanLin.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
      finrank_euclideanSpace i
  calc
    (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (rightSingularBasis A i) =
        (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
          finrank_euclideanSpace i : ℂ) • rightSingularBasis A i := by
      simp [rightSingularBasis, h]
    _ = ((matrixSingularValues A i : ℂ) ^ 2) • rightSingularBasis A i := by
      rw [← A.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace i]
      simp [matrixSingularValues]

noncomputable def leftSingularVector (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) : EuclideanSpace ℂ O :=
  ((matrixSingularValues A i : ℂ)⁻¹) • A.toEuclideanLin (rightSingularBasis A i)

theorem norm_apply_rightSingularBasis (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    ‖A.toEuclideanLin (rightSingularBasis A i)‖ = matrixSingularValues A i := by
  have hv : A.toEuclideanLin.adjoint (A.toEuclideanLin (rightSingularBasis A i)) =
      ((matrixSingularValues A i : ℂ) ^ 2) • rightSingularBasis A i := by
    simpa only [LinearMap.comp_apply] using adjoint_comp_apply_rightSingularBasis A i
  have hinner : inner ℂ (A.toEuclideanLin (rightSingularBasis A i))
      (A.toEuclideanLin (rightSingularBasis A i)) = (matrixSingularValues A i : ℂ) ^ 2 := by
    rw [← A.toEuclideanLin.adjoint_inner_right, hv, inner_smul_right]
    simp
  have hsq : ‖A.toEuclideanLin (rightSingularBasis A i)‖ ^ 2 =
      (matrixSingularValues A i) ^ 2 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K] using! hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (matrixSingularValues_nonneg A i)).mp hsq

theorem apply_rightSingularBasis_eq_zero (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) (hσ : matrixSingularValues A i = 0) :
    A.toEuclideanLin (rightSingularBasis A i) = 0 := by
  apply norm_eq_zero.mp
  rw [norm_apply_rightSingularBasis, hσ]

theorem leftSingularVector_eq_zero (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) (hσ : matrixSingularValues A i = 0) :
    leftSingularVector A i = 0 := by
  simp [leftSingularVector, hσ]

theorem apply_rightSingularBasis_eq_smul_leftSingularVector (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    A.toEuclideanLin (rightSingularBasis A i) =
      (matrixSingularValues A i : ℂ) • leftSingularVector A i := by
  by_cases hσReal : matrixSingularValues A i = 0
  · simp [hσReal, apply_rightSingularBasis_eq_zero A i hσReal]
  · have hσ : (matrixSingularValues A i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσReal
    unfold leftSingularVector
    rw [smul_smul, mul_inv_cancel₀ hσ, one_smul]

theorem adjoint_apply_leftSingularVector (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    A.toEuclideanLin.adjoint (leftSingularVector A i) =
      (matrixSingularValues A i : ℂ) • rightSingularBasis A i := by
  by_cases hσReal : matrixSingularValues A i = 0
  · simp [leftSingularVector_eq_zero A i hσReal, hσReal]
  · have hσ : (matrixSingularValues A i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσReal
    have hv : A.toEuclideanLin.adjoint (A.toEuclideanLin (rightSingularBasis A i)) =
        ((matrixSingularValues A i : ℂ) ^ 2) • rightSingularBasis A i := by
      simpa only [LinearMap.comp_apply] using adjoint_comp_apply_rightSingularBasis A i
    unfold leftSingularVector
    rw [map_smul, hv, smul_smul, pow_two, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]

theorem rightSingularBasis_singularPair (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    A.toEuclideanLin (rightSingularBasis A i) =
        (matrixSingularValues A i : ℂ) • leftSingularVector A i ∧
      A.toEuclideanLin.adjoint (leftSingularVector A i) =
        (matrixSingularValues A i : ℂ) • rightSingularBasis A i :=
  ⟨apply_rightSingularBasis_eq_smul_leftSingularVector A i,
    adjoint_apply_leftSingularVector A i⟩

theorem norm_leftSingularVector (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) (hi : (i : ℕ) < finrank ℂ A.toEuclideanLin.range) :
    ‖leftSingularVector A i‖ = 1 := by
  have hσ : 0 < matrixSingularValues A i :=
    (matrixSingularValues_pos_iff_lt_finrank_range A).2 hi
  rw [leftSingularVector, norm_smul, norm_inv, norm_apply_rightSingularBasis,
    Complex.norm_real, Real.norm_of_nonneg hσ.le]
  exact inv_mul_cancel₀ (ne_of_gt hσ)

theorem inner_leftSingularVector_of_ne (A : Matrix O I ℂ)
    {i j : Fin (Fintype.card I)} (hij : i ≠ j) :
    inner ℂ (leftSingularVector A i) (leftSingularVector A j) = 0 := by
  have hv : A.toEuclideanLin.adjoint (A.toEuclideanLin (rightSingularBasis A j)) =
      ((matrixSingularValues A j : ℂ) ^ 2) • rightSingularBasis A j := by
    simpa only [LinearMap.comp_apply] using adjoint_comp_apply_rightSingularBasis A j
  unfold leftSingularVector
  rw [inner_smul_left, inner_smul_right, ← A.toEuclideanLin.adjoint_inner_right, hv,
    inner_smul_right, (rightSingularBasis A).inner_eq_zero hij]
  simp

theorem orthonormal_leftSingularVector (A : Matrix O I ℂ) :
    Orthonormal ℂ (fun i : {i : Fin (Fintype.card I) //
      (i : ℕ) < finrank ℂ A.toEuclideanLin.range} => leftSingularVector A i.1) := by
  constructor
  · intro i
    exact norm_leftSingularVector A i.1 i.2
  · intro i j hij
    exact inner_leftSingularVector_of_ne A (fun h => hij (Subtype.ext h))

theorem apply_eq_sum_singularVectors (A : Matrix O I ℂ) (x : EuclideanSpace ℂ I) :
    A.toEuclideanLin x = ∑ i : Fin (Fintype.card I),
      (inner ℂ (rightSingularBasis A i) x * (matrixSingularValues A i : ℂ)) •
        leftSingularVector A i := by
  calc
    A.toEuclideanLin x = A.toEuclideanLin
        (∑ i : Fin (Fintype.card I), inner ℂ (rightSingularBasis A i) x •
          rightSingularBasis A i) := congrArg A.toEuclideanLin
            ((rightSingularBasis A).sum_repr' x).symm
    _ = ∑ i : Fin (Fintype.card I),
        (inner ℂ (rightSingularBasis A i) x * (matrixSingularValues A i : ℂ)) •
          leftSingularVector A i := by
      simp only [map_sum, map_smul, apply_rightSingularBasis_eq_smul_leftSingularVector,
        smul_smul]

theorem toEuclideanLin_eq_sum_rankOne (A : Matrix O I ℂ) :
    A.toEuclideanLin = ∑ i : Fin (Fintype.card I), (matrixSingularValues A i : ℂ) •
      (InnerProductSpace.rankOne ℂ (leftSingularVector A i)
        (rightSingularBasis A i)).toLinearMap := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, smul_smul, mul_comm] using
      apply_eq_sum_singularVectors A x

theorem matrix_eq_sum_singularVectors (A : Matrix O I ℂ) :
    A = ∑ i : Fin (Fintype.card I), (matrixSingularValues A i : ℂ) •
      Matrix.vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i)) := by
  have h := congrArg Matrix.toEuclideanLin.symm (toEuclideanLin_eq_sum_rankOne A)
  simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul,
    InnerProductSpace.symm_toEuclideanLin_rankOne] using h

private noncomputable def leftSingularSeed (A : Matrix O I ℂ)
    (i : Fin (Fintype.card O)) : EuclideanSpace ℂ O :=
  if hi : (i : ℕ) < Fintype.card I then leftSingularVector A ⟨i, hi⟩ else 0

private theorem leftSingularSeed_orthonormal (A : Matrix O I ℂ) :
    Orthonormal ℂ (({i : Fin (Fintype.card O) |
      (i : ℕ) < finrank ℂ A.toEuclideanLin.range} : Set _).restrict (leftSingularSeed A)) := by
  constructor
  · intro i
    have hI : (i.1 : ℕ) < Fintype.card I :=
      lt_of_lt_of_le i.2 (by simpa using A.toEuclideanLin.finrank_range_le)
    change ‖leftSingularSeed A i.1‖ = 1
    rw [leftSingularSeed, dif_pos hI]
    exact norm_leftSingularVector A ⟨i.1, hI⟩ i.2
  · intro i j hij
    have hI : (i.1 : ℕ) < Fintype.card I :=
      lt_of_lt_of_le i.2 (by simpa using A.toEuclideanLin.finrank_range_le)
    have hJ : (j.1 : ℕ) < Fintype.card I :=
      lt_of_lt_of_le j.2 (by simpa using A.toEuclideanLin.finrank_range_le)
    change inner ℂ (leftSingularSeed A i.1) (leftSingularSeed A j.1) = 0
    rw [leftSingularSeed, dif_pos hI, leftSingularSeed, dif_pos hJ]
    apply inner_leftSingularVector_of_ne A
    intro h
    have hv : (i.1 : ℕ) = (j.1 : ℕ) :=
      congrArg (fun k : Fin (Fintype.card I) => (k : ℕ)) h
    exact hij (Subtype.ext (Fin.ext hv))

private theorem exists_leftSingularBasis (A : Matrix O I ℂ) :
    ∃ b : OrthonormalBasis (Fin (Fintype.card O)) ℂ (EuclideanSpace ℂ O),
      ∀ i : Fin (Fintype.card O), (i : ℕ) < finrank ℂ A.toEuclideanLin.range →
        b i = leftSingularSeed A i := by
  exact Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (leftSingularSeed_orthonormal A)

noncomputable def leftSingularBasis (A : Matrix O I ℂ) :
    OrthonormalBasis (Fin (Fintype.card O)) ℂ (EuclideanSpace ℂ O) :=
  Classical.choose (exists_leftSingularBasis A)

theorem leftSingularBasis_apply_of_lt (A : Matrix O I ℂ)
    (i : Fin (Fintype.card O)) (hi : (i : ℕ) < finrank ℂ A.toEuclideanLin.range) :
    leftSingularBasis A i = leftSingularVector A
      ⟨i, lt_of_lt_of_le hi (by simpa using A.toEuclideanLin.finrank_range_le)⟩ := by
  have hI : (i : ℕ) < Fintype.card I :=
    lt_of_lt_of_le hi (by simpa using A.toEuclideanLin.finrank_range_le)
  simpa only [leftSingularSeed, dif_pos hI] using!
    (Classical.choose_spec (exists_leftSingularBasis A)) i hi

theorem toMatrix_singularBases (A : Matrix O I ℂ) :
    LinearMap.toMatrix (rightSingularBasis A).toBasis (leftSingularBasis A).toBasis
      A.toEuclideanLin =
      (Matrix.of fun (j : Fin (Fintype.card O)) (i : Fin (Fintype.card I)) =>
        if (j : ℕ) = (i : ℕ) then (matrixSingularValues A i : ℂ) else 0) := by
  ext j i
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
  by_cases hi : (i : ℕ) < finrank ℂ A.toEuclideanLin.range
  · have hO : (i : ℕ) < Fintype.card O :=
      lt_of_lt_of_le hi (by simpa using Submodule.finrank_le A.toEuclideanLin.range)
    let k : Fin (Fintype.card O) := ⟨i, hO⟩
    have hk : leftSingularBasis A k = leftSingularVector A i := by
      simpa only [k] using leftSingularBasis_apply_of_lt A k hi
    rw [apply_rightSingularBasis_eq_smul_leftSingularVector, ← hk, inner_smul_right,
      (leftSingularBasis A).inner_eq_ite]
    by_cases hji : (j : ℕ) = (i : ℕ)
    · have hjk : j = k := Fin.ext hji
      simp [hjk, k]
    · have hjk : j ≠ k := fun h => hji (congrArg Fin.val h)
      simp [hji, hjk]
  · have hσ : matrixSingularValues A i = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (le_of_not_gt hi)
    rw [apply_rightSingularBasis_eq_zero A i hσ, inner_zero_right]
    simp [hσ]

theorem toEuclideanLin_svd (A : Matrix O I ℂ) :
    A.toEuclideanLin = Matrix.toLin (rightSingularBasis A).toBasis (leftSingularBasis A).toBasis
      (Matrix.of fun (j : Fin (Fintype.card O)) (i : Fin (Fintype.card I)) =>
        if (j : ℕ) = (i : ℕ) then (matrixSingularValues A i : ℂ) else 0) := by
  rw [← toMatrix_singularBases A, Matrix.toLin_toMatrix]

theorem adjoint_apply_leftSingularBasis_of_rank_le (A : Matrix O I ℂ)
    (j : Fin (Fintype.card O)) (hj : finrank ℂ A.toEuclideanLin.range ≤ (j : ℕ)) :
    A.toEuclideanLin.adjoint (leftSingularBasis A j) = 0 := by
  apply InnerProductSpace.ext_inner_left_basis (rightSingularBasis A).toBasis
  intro i
  change inner ℂ (rightSingularBasis A i)
    (A.toEuclideanLin.adjoint (leftSingularBasis A j)) =
      inner ℂ (rightSingularBasis A i) 0
  rw [inner_zero_right, A.toEuclideanLin.adjoint_inner_right]
  by_cases hi : (i : ℕ) < finrank ℂ A.toEuclideanLin.range
  · have hO : (i : ℕ) < Fintype.card O :=
      lt_of_lt_of_le hi (by simpa using Submodule.finrank_le A.toEuclideanLin.range)
    let k : Fin (Fintype.card O) := ⟨i, hO⟩
    have hk : leftSingularBasis A k = leftSingularVector A i := by
      simpa only [k] using leftSingularBasis_apply_of_lt A k hi
    have hkj : k ≠ j := by
      intro h
      have heq : (i : ℕ) = (j : ℕ) := congrArg Fin.val h
      exact (ne_of_lt (lt_of_lt_of_le hi hj)) heq
    rw [apply_rightSingularBasis_eq_smul_leftSingularVector, ← hk,
      inner_smul_left, (leftSingularBasis A).inner_eq_zero hkj, mul_zero]
  · have hσ : matrixSingularValues A i = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (le_of_not_gt hi)
    rw [apply_rightSingularBasis_eq_zero A i hσ, inner_zero_left]

theorem matrixSingularValues_exists_singularPair (A : Matrix O I ℂ) {i : ℕ}
    (hi : i < finrank ℂ A.toEuclideanLin.range) :
    ∃ (u : EuclideanSpace ℂ O) (v : EuclideanSpace ℂ I),
      Module.End.HasEigenvector (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin)
          ((matrixSingularValues A i : ℂ) ^ 2) v ∧
      A.toEuclideanLin v = (matrixSingularValues A i : ℂ) • u ∧
      A.toEuclideanLin.adjoint u = (matrixSingularValues A i : ℂ) • v := by
  let σ : ℂ := matrixSingularValues A i
  have hσReal : matrixSingularValues A i ≠ 0 :=
    ne_of_gt ((matrixSingularValues_pos_iff_lt_finrank_range A).2 hi)
  have hσ : σ ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hσReal
  have hiDomain : i < finrank ℂ (EuclideanSpace ℂ I) :=
    lt_of_lt_of_le hi A.toEuclideanLin.finrank_range_le
  have heig : Module.End.HasEigenvalue
      (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (σ ^ 2) := by
    simpa [σ, matrixSingularValues] using
      (A.toEuclideanLin.hasEigenvalue_adjoint_comp_self_sq_singularValues
        (n := i) hiDomain)
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let u : EuclideanSpace ℂ O := σ⁻¹ • A.toEuclideanLin v
  refine ⟨u, v, hv, ?_, ?_⟩
  · dsimp [u]
    change A.toEuclideanLin v = σ • (σ⁻¹ • A.toEuclideanLin v)
    rw [smul_smul, mul_inv_cancel₀ hσ, one_smul]
  · have hv' :
        A.toEuclideanLin.adjoint (A.toEuclideanLin v) = σ ^ 2 • v := by
      simpa using hv.apply_eq_smul
    dsimp [u]
    rw [map_smul, hv']
    change σ⁻¹ • (σ ^ 2 • v) = σ • v
    rw [smul_smul, pow_two, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]

variable [DecidableEq O]

theorem toEuclideanLin_gram (A : Matrix O I ℂ) :
    (Aᴴ * A).toEuclideanLin =
      A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin := by
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem gram_apply_rightSingularBasis (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) :
    (Aᴴ * A).toEuclideanLin (rightSingularBasis A i) =
      ((matrixSingularValues A i : ℂ) ^ 2) • rightSingularBasis A i := by
  rw [toEuclideanLin_gram]
  exact adjoint_comp_apply_rightSingularBasis A i

theorem matrixSingularValues_sq_hasEigenvalue_gram (A : Matrix O I ℂ) {i : ℕ}
    (hi : i < Fintype.card I) :
    Module.End.HasEigenvalue (Aᴴ * A).toEuclideanLin
      ((matrixSingularValues A i : ℂ) ^ 2) := by
  rw [toEuclideanLin_gram]
  simpa [matrixSingularValues] using
    (A.toEuclideanLin.hasEigenvalue_adjoint_comp_self_sq_singularValues
      (n := i) (by simpa using hi))

end SingularValueBridge

end Qatlib.Concepts.RandCompile.ChannelBudget
