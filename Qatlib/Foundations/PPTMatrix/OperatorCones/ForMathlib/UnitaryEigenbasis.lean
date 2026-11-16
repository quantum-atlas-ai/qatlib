/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.GurvitsBarnumCore
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section




/-!
# An orthonormal unitary eigenbasis and its rank-one qubit product identity.

A finite complex unitary has an orthonormal eigenbasis whose eigenvalues have modulus one. The simultaneous Hermitian spectral decomposition supplies the basis, and the resulting phase decomposition gives a sum of positive product operators for its qubit block matrix.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptEigenbasis

/-- Establishes `cartesian_re_hermitian`: `((1 / 2 : ℂ) • (W + Wᴴ)).IsHermitian`, for the stated parameters. -/
private theorem cartesian_re_hermitian {n : Type*} (W : Matrix n n ℂ) :
    ((1 / 2 : ℂ) • (W + Wᴴ)).IsHermitian := by
  have hstar : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (W + Wᴴ))ᴴ = (1 / 2 : ℂ) • (W + Wᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, hstar, add_comm Wᴴ W]

/-- Establishes `cartesian_im_hermitian`: `((-Complex.I / 2) • (W - Wᴴ)).IsHermitian`, for the stated parameters. -/
private theorem cartesian_im_hermitian {n : Type*} (W : Matrix n n ℂ) :
    ((-Complex.I / 2) • (W - Wᴴ)).IsHermitian := by
  have hstar : star (-Complex.I / 2) = Complex.I / 2 := by simp
  show ((-Complex.I / 2) • (W - Wᴴ))ᴴ = (-Complex.I / 2) • (W - Wᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, hstar]
  module

/-- Establishes `cartesian_reconstruct`: `(1 / 2 : ℂ) • (W + Wᴴ) + Complex.I • ((-Complex.I / 2) • (W - Wᴴ)) = W`, for the stated parameters. -/
private theorem cartesian_reconstruct {n : Type*} (W : Matrix n n ℂ) :
    (1 / 2 : ℂ) • (W + Wᴴ) + Complex.I • ((-Complex.I / 2) • (W - Wᴴ)) = W := by
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  rw [smul_smul, hI]
  module

/-- Establishes `cartesian_parts_commute`: `Commute ((1 / 2 : ℂ) • (W + Wᴴ)) ((-Complex.I / 2) • (W - Wᴴ))`, for the stated parameters. -/
private theorem cartesian_parts_commute {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    Commute ((1 / 2 : ℂ) • (W + Wᴴ)) ((-Complex.I / 2) • (W - Wᴴ)) := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hMP : (W - Wᴴ) * (W + Wᴴ) = (W + Wᴴ) * (W - Wᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.mul_sub, hW, hW']
    abel
  change ((1 / 2 : ℂ) • (W + Wᴴ)) * ((-Complex.I / 2) • (W - Wᴴ)) =
    ((-Complex.I / 2) • (W - Wᴴ)) * ((1 / 2 : ℂ) • (W + Wᴴ))
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hMP, mul_comm (-Complex.I / 2) (1 / 2 : ℂ)]

/-- Every finite-dimensional complex unitary has a genuine orthonormal
column eigenbasis. There is no spectral-basis assumption in this theorem. -/
theorem exists_unitary_column_eigenbasis (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : Wᴴ * W = 1) :
    ∃ (U : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ j, star (c j) * c j = 1) ∧ (∀ j, ‖c j‖ = 1) ∧
      W * U = U * Matrix.diagonal c := by
  classical
  let A : Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • (W + Wᴴ)
  let B : Matrix (Fin d) (Fin d) ℂ := (-Complex.I / 2) • (W - Wᴴ)
  have hA : A.IsHermitian := cartesian_re_hermitian W
  have hB : B.IsHermitian := cartesian_im_hermitian W
  have hAB : Commute A B := cartesian_parts_commute W hW
  have hAs : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hBs : B.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hABs : Commute A.toEuclideanLin B.toEuclideanLin := by
    change A.toEuclideanLin ∘ₗ B.toEuclideanLin =
      B.toEuclideanLin ∘ₗ A.toEuclideanLin
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg (Matrix.toLpLin 2 2) hAB.eq
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := by simp
  let J : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin d)) := fun i =>
    Module.End.eigenspace A.toEuclideanLin i.2 ⊓
      Module.End.eigenspace B.toEuclideanLin i.1
  have hdecomp : DirectSum.IsInternal J :=
    hAs.directSum_isInternal_of_commute hBs hABs
  have hfinite : Set.Finite {i | J i ≠ ⊥} :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hdecomp.submodule_iSupIndep
  let I : Type := {i : ℂ × ℂ // J i ≠ ⊥}
  let : Fintype I := hfinite.fintype
  have hdecomp' : DirectSum.IsInternal (fun i : I => J i.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr hdecomp
  have horth : OrthogonalFamily ℂ (fun i : I => J i.val)
      (fun i => (J i.val).subtypeₗᵢ) :=
    (hAs.orthogonalFamily_eigenspace_inf_eigenspace hBs).comp Subtype.val_injective
  let b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)) :=
    hdecomp'.subordinateOrthonormalBasis hn horth
  let idx : Fin d → ℂ × ℂ := fun j =>
    (hdecomp'.subordinateOrthonormalBasisIndex hn j horth).val
  let c : Fin d → ℂ := fun j => (idx j).2 + Complex.I * (idx j).1
  have hbA (j : Fin d) : A.toEuclideanLin (b j) = (idx j).2 • b j := by
    have hj : b j ∈ J (idx j) :=
      hdecomp'.subordinateOrthonormalBasis_subordinate hn j horth
    exact Module.End.mem_eigenspace_iff.mp hj.1
  have hbB (j : Fin d) : B.toEuclideanLin (b j) = (idx j).1 • b j := by
    have hj : b j ∈ J (idx j) :=
      hdecomp'.subordinateOrthonormalBasis_subordinate hn j horth
    exact Module.End.mem_eigenspace_iff.mp hj.2
  have hrec : A + Complex.I • B = W := cartesian_reconstruct W
  have hbW (j : Fin d) : W.toEuclideanLin (b j) = c j • b j := by
    rw [← hrec]
    change (Matrix.toEuclideanLin (A + Complex.I • B)) (b j) =
      ((idx j).2 + Complex.I * (idx j).1) • b j
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hbA, hbB, smul_smul, add_smul]
  let U : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => b j i
  have hU : Uᴴ * U = 1 := by
    change ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis)ᴴ *
      (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis = 1
    exact (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hWU : W * U = U * Matrix.diagonal c := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal]
    have hj := congrArg (fun x : EuclideanSpace ℂ (Fin d) => x i) (hbW j)
    change (∑ k, W i k * b j k) = c j * b j i at hj
    change (∑ k, W i k * b j k) = b j i * c j
    exact hj.trans (mul_comm _ _)
  have hD : (Matrix.diagonal c)ᴴ * Matrix.diagonal c = 1 := by
    calc
      (Matrix.diagonal c)ᴴ * Matrix.diagonal c =
          (U * Matrix.diagonal c)ᴴ * (U * Matrix.diagonal c) := by
        calc
          (Matrix.diagonal c)ᴴ * Matrix.diagonal c =
              (Matrix.diagonal c)ᴴ * (Uᴴ * U) * Matrix.diagonal c := by
            rw [hU, Matrix.mul_one]
          _ = (U * Matrix.diagonal c)ᴴ * (U * Matrix.diagonal c) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (W * U)ᴴ * (W * U) := by rw [hWU]
      _ = 1 := by
        calc
          (W * U)ᴴ * (W * U) = Uᴴ * (Wᴴ * W) * U := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [hW, Matrix.mul_one, hU]
  have hc (j : Fin d) : star (c j) * c j = 1 := by
    have hj := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j j) hD
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply] using hj
  have hnorm (j : Fin d) : ‖c j‖ = 1 := by
    have hj : ‖c j‖ * ‖c j‖ = 1 := by
      simpa only [norm_mul, norm_star, norm_one] using congrArg norm (hc j)
    nlinarith [norm_nonneg (c j)]
  exact ⟨U, c, hU, hU', hc, hnorm, hWU⟩

/-- The rank-one reference projector fixes the conjugation convention in Eq.(6). -/
theorem pure_reference_vector (c : ℂ) (hc : star c * c = 1) :
    pureState (![1, star c] : Fin 2 → ℂ) =
      (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pureState, Matrix.vecMulVec_apply]
  change star c * c = 1
  exact hc

/-- The literal product identity for prescribed unitary eigenvector columns.
The basis is supplied as U (not replaced by arbitrary positive matrices). -/
theorem qubit_unitary_eq_sum_pure_products_of_eigenbasis
    (d : ℕ) (W U : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ)
    (hU : Uᴴ * U = 1) (hc : ∀ j, star (c j) * c j = 1)
    (hWU : W * U = U * Matrix.diagonal c) :
    qubitBlocks (1 : Matrix (Fin d) (Fin d) ℂ) W Wᴴ 1 =
      ∑ j, pureState (![1, star (c j)] : Fin 2 → ℂ) ⊗ₖ
        pureState (fun i : Fin d => U i j) := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hspec : U * Matrix.diagonal c * Uᴴ = W := by
    rw [← hWU, Matrix.mul_assoc, hU', Matrix.mul_one]
  have hsum : (∑ j, pureState (fun i : Fin d => U i j)) =
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [← hU']
    apply Matrix.ext
    intro i k
    simp only [Matrix.sum_apply, pureState, Matrix.vecMulVec_apply,
      Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hweighted : (∑ j, c j • pureState (fun i : Fin d => U i j)) = W := by
    rw [← hspec]
    apply Matrix.ext
    intro i k
    have hentry : (U * Matrix.diagonal c * Uᴴ) i k =
        ∑ j, (U i j * c j) * star (U k j) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [hentry]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pureState,
      Matrix.vecMulVec_apply, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hadjoint : (∑ j, star (c j) • pureState (fun i : Fin d => U i j)) = Wᴴ := by
    rw [← hweighted, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hP : (pureState (fun i : Fin d => U i j)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star _
    rw [Matrix.conjTranspose_smul, hP.isHermitian.eq]
  calc
    qubitBlocks (1 : Matrix (Fin d) (Fin d) ℂ) W Wᴴ 1 =
        qubitBlocks (∑ j, pureState (fun i : Fin d => U i j))
          (∑ j, c j • pureState (fun i : Fin d => U i j))
          (∑ j, star (c j) • pureState (fun i : Fin d => U i j))
          (∑ j, pureState (fun i : Fin d => U i j)) := by
      rw [hsum, hweighted, hadjoint]
    _ = ∑ j, pureState (![1, star (c j)] : Fin 2 → ℂ) ⊗ₖ
        pureState (fun i : Fin d => U i j) := by
      rw [qubitBlocks_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pure_reference_vector (c j) (hc j), two_by_two_kronecker]

/-- Eq.(6) with the eigenbasis existence discharged, for every finite-dimensional
complex unitary W. The same U,c satisfy eigenvector and product identities. -/
theorem exists_unitary_eigenbasis_product_identity
    (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (U : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ j, ‖c j‖ = 1) ∧ W * U = U * Matrix.diagonal c ∧
      qubitBlocks (1 : Matrix (Fin d) (Fin d) ℂ) W Wᴴ 1 =
        ∑ j, pureState (![1, star (c j)] : Fin 2 → ℂ) ⊗ₖ
          pureState (fun i : Fin d => U i j) := by
  obtain ⟨U, c, hU, hU', hc, hnorm, hWU⟩ := exists_unitary_column_eigenbasis d W hW
  exact ⟨U, c, hU, hU', hnorm, hWU,
    qubit_unitary_eq_sum_pure_products_of_eigenbasis d W U c hU hc hWU⟩

/-- The literal real-phase presentation in manuscript Eq.(6). The negative
phase in the reference vector is essential to the upper-right block W. -/
theorem exists_unitary_phase_product_identity
    (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (U : Matrix (Fin d) (Fin d) ℂ) (θ : Fin d → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      W * U = U * Matrix.diagonal (fun j => Complex.exp ((θ j : ℂ) * Complex.I)) ∧
      qubitBlocks (1 : Matrix (Fin d) (Fin d) ℂ) W Wᴴ 1 =
        ∑ j, pureState (![1, Complex.exp (-((θ j : ℂ) * Complex.I))] : Fin 2 → ℂ) ⊗ₖ
          pureState (fun i : Fin d => U i j) := by
  obtain ⟨U, c, hU, hU', hnorm, hWU, hsum⟩ :=
    exists_unitary_eigenbasis_product_identity d W hW
  let θ : Fin d → ℝ := fun j => Complex.arg (c j)
  have hphase (j : Fin d) : Complex.exp ((θ j : ℂ) * Complex.I) = c j := by
    simpa only [hnorm j, Complex.ofReal_one, one_mul] using
      Complex.norm_mul_exp_arg_mul_I (c j)
  have hconj (j : Fin d) :
      Complex.exp (-((θ j : ℂ) * Complex.I)) = star (c j) := by
    change Complex.exp (-((θ j : ℂ) * Complex.I)) = (starRingEnd ℂ) (c j)
    rw [← hphase j, ← Complex.exp_conj]
    congr 1
    simp
  refine ⟨U, θ, hU, hU', ?_, ?_⟩
  · simpa only [hphase] using hWU
  · simpa only [hconj] using hsum

/-- The separability consequence is proved through the literal eigenbasis
product decomposition, so Eq.(6) belongs to this corollary's proof closure. -/
theorem isSeparable_qubit_unitary_from_eigenbasis
    (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    IsSeparable (qubitBlocks (1 : Matrix (Fin d) (Fin d) ℂ) W Wᴴ 1) := by
  obtain ⟨U, θ, _, _, _, hsum⟩ :=
    exists_unitary_phase_product_identity d W hW
  rw [hsum]
  exact isSeparable_sum_kronecker _ _
    (fun j => Matrix.posSemidef_vecMulVec_self_star _)
    (fun j => Matrix.posSemidef_vecMulVec_self_star _)

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptEigenbasis
