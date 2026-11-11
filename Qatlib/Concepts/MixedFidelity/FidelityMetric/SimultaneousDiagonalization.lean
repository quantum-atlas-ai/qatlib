/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Simultaneous diagonalization of commuting Hermitian matrices

This module constructs a common orthonormal eigenbasis for commuting symmetric endomorphisms and
converts it into a simultaneous unitary diagonalization of Hermitian matrices. Both arbitrary
finite matrix indices and indices of the form `Fin n` are supported. See [Bhatia1997] for the
spectral-theoretic background.

## Main statements

* `exists_common_orthonormal_eigenbasis`: constructs a common eigenbasis with real eigenvalues.
* `exists_simultaneous_unitary_diagonalization`: diagonalizes a finite commuting Hermitian
  family.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped Classical BigOperators Matrix

/-- A pairwise commuting family of symmetric endomorphisms of a finite-dimensional complex inner
product space has a common orthonormal eigenbasis with real eigenvalues, indexed by `Fin n`
when the dimension is `n`. -/
theorem exists_common_orthonormal_eigenbasis {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : ι → Module.End ℂ E) (hT : ∀ a,(T a).IsSymmetric)
    (hComm : ∀ a b,T a*T b=T b*T a) (n : ℕ) (hn : Module.finrank ℂ E=n) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ E) (lam : ι → Fin n → ℝ),
      ∀ a j,T a (b j)=(lam a j : ℂ) • b j := by
  let V := fun χ : ι → ℂ => ⨅ a,Module.End.eigenspace (T a) (χ a)
  have hC : Pairwise (Function.onFun Commute T) := fun a b _ => hComm a b
  have hInt : DirectSum.IsInternal V :=
      LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC
  let S := {χ : ι → ℂ | V χ≠⊥}
  have hs : S.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hInt.submodule_iSupIndep
  letI : Fintype S := hs.fintype
  have horth0 := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have horth : OrthogonalFamily ℂ (fun χ : S => V χ) (fun χ => (V χ).subtypeₗᵢ) := by
    intro χ ψ hne x y
    exact horth0 (fun h => hne (Subtype.ext h)) x y
  have hsup : (⨆ χ : S,V χ)=⊤ := by
    apply le_antisymm le_top
    rw [← hInt.submodule_iSup_eq_top]
    apply iSup_le
    intro χ
    by_cases hχ : V χ=⊥
    · rw [hχ]
      exact bot_le
    · exact le_iSup (fun ψ : S => V ψ) ⟨χ,hχ⟩
  have hactive : DirectSum.IsInternal (fun χ : S => V χ) :=
    horth.isInternal_iff.mpr (by rw [hsup,Submodule.top_orthogonal_eq_bot])
  let b := hactive.subordinateOrthonormalBasis hn horth
  let χ := fun j : Fin n => (hactive.subordinateOrthonormalBasisIndex hn j horth).val
  have hmem (a : ι) (j : Fin n) : b j∈Module.End.eigenspace (T a) (χ j a) := by
    have h := hactive.subordinateOrthonormalBasis_subordinate hn j horth
    exact (Submodule.mem_iInf (fun a => Module.End.eigenspace (T a) (χ j a))).mp h a
  have hreal (a : ι) (j : Fin n) : χ j a=((χ j a).re : ℂ) := by
    have he := Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem a j,b.toBasis.ne_zero j⟩
    have hc := (hT a).conj_eigenvalue_eq_self he
    have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    apply Complex.ext
    · rfl
    · change (χ j a).im=0
      linarith
  refine ⟨b,(fun a j => (χ j a).re),?_⟩
  intro a j
  have h := Module.End.mem_eigenspace_iff.mp (hmem a j)
  rw [hreal a j] at h
  exact h

/-- A pairwise commuting family of Hermitian matrices on a finite index type has a common
unitary diagonalization with real diagonal entries, using `Fin (Fintype.card J)` for the
eigenbasis. -/
theorem exists_simultaneous_unitary_diagonalization_index {J ι : Type*} [Fintype J] [DecidableEq J]
    (C : ι → Matrix J J ℂ) (hHerm : ∀ a,(C a).IsHermitian)
    (hComm : ∀ a b,C a*C b=C b*C a) :
    ∃ (U : Matrix J (Fin (Fintype.card J)) ℂ) (diag : ι → Fin (Fintype.card J) → ℝ),
      U*U.conjTranspose=1 ∧ U.conjTranspose*U=1 ∧
        ∀ a,C a=U*Matrix.diagonal (fun i => (diag a i : ℂ))*U.conjTranspose := by
  let T := fun a => (C a).toEuclideanLin
  have hT (a : ι) : (T a).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hHerm a)
  have hTC (a b : ι) : T a*T b=T b*T a := by
    apply LinearMap.ext
    intro x
    change (C a).toEuclideanLin ((C b).toEuclideanLin x)=(C b).toEuclideanLin
        ((C a).toEuclideanLin x)
    apply WithLp.ofLp_injective
    change C a*ᵥ(C b*ᵥx.ofLp)=C b*ᵥ(C a*ᵥx.ofLp)
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hComm a b]
  obtain ⟨b,diag,heigen⟩ := exists_common_orthonormal_eigenbasis T hT hTC (Fintype.card J) (by simp)
  let U := (EuclideanSpace.basisFun J ℂ).toBasis.toMatrix b
  have hU (i : J) (j : Fin (Fintype.card J)) : U i j=(b j) i := by
    simp only [U,Module.Basis.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
  have hleft : U*U.conjTranspose=1 :=
    (EuclideanSpace.basisFun J ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hright : U.conjTranspose*U=1 :=
    (EuclideanSpace.basisFun J ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  refine ⟨U,diag,hleft,hright,?_⟩
  intro a
  have hCU : C a*U=U*Matrix.diagonal (fun j => (diag a j : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    change (∑ l : J,C a i l*U l j)=U i j*(diag a j : ℂ)
    simp_rw [hU]
    have h := congrArg (fun x : EuclideanSpace ℂ J => x i) (heigen a j)
    change (∑ l : J,C a i l*(b j) l)=(diag a j : ℂ)*(b j) i at h
    exact h.trans (mul_comm _ _)
  calc
    _ = C a*(U*U.conjTranspose) := by rw [hleft,Matrix.mul_one]
    _ = (C a*U)*U.conjTranspose := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [hCU]

/-- A finite pairwise commuting family of Hermitian `n × n` matrices has a common unitary
diagonalization with real diagonal entries. -/
theorem exists_simultaneous_unitary_diagonalization {n : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → Matrix (Fin n) (Fin n) ℂ) (hHerm : ∀ a,(C a).IsHermitian)
    (hComm : ∀ a b,C a*C b=C b*C a) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (diag : ι → Fin n → ℝ),
      U*U.conjTranspose=1 ∧ U.conjTranspose*U=1 ∧
        ∀ a,C a=U*Matrix.diagonal (fun i => (diag a i : ℂ))*U.conjTranspose := by
  have h := exists_simultaneous_unitary_diagonalization_index C hHerm hComm
  rw [Fintype.card_fin] at h
  exact h
end Qatlib.Concepts.MixedFidelity.FidelityMetric
