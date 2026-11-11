/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Moments

/-!
# LCU embeddings and matrix compression

`embedding` places a system vector into an auxiliary register with real amplitudes `β`, and
`select` applies a system matrix conditioned on that register. `compression` identifies the
compressed SELECT matrix with the weighted Hamiltonian `ham`.

For weights whose squares sum to one, the embedding is isometric and its adjoint recovers the
source vector. The module also proves the algebraic SELECT identities and adjoint actions on the
associated frame vectors, providing finite LCU frame calculations for [PoulinEtAl2018].

## Main statements

* `embedding_gram`: normalized real weights make the embedding an isometry.
* `compression`: the embedding compresses SELECT to `ham`.
* `embedding_adjoint_phi1`: the auxiliary frame vector lies in the kernel of the embedding
  adjoint under the eigenvector equation.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The rectangular matrix embedding a system coordinate vector into the auxiliary register with
real amplitudes `β`. -/
def embedding (β : J → ℝ) : Matrix (J × I) I ℂ :=
  fun ji x => if ji.2=x then (β ji.1 : ℂ) else 0

/-- The block-diagonal matrix applying `P j` on the system coordinates within auxiliary branch
`j`. -/
def select (P : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  fun ji kl => if ji.1=kl.1 then P ji.1 ji.2 kl.2 else 0

omit [Fintype J] [DecidableEq J] in

/-- The embedding sends a system state `φ` to the frame vector `phi0 β φ`. -/
theorem embedding_mulVec (β : J → ℝ) (φ : State I) : embedding (I := I) β *ᵥ φ = phi0 β φ := by
  ext ji
  simp [embedding, phi0, Matrix.mulVec, dotProduct]

omit [DecidableEq I] in

/-- At auxiliary index `j`, SELECT acts on the system slice by the matrix `P j`. -/
theorem select_mulVec (P : J → Matrix I I ℂ) (ψ : State (J × I)) (j : J) (i : I) :
    (select P *ᵥ ψ) (j,i) = ∑ x, P j i x * ψ (j,x) := by
  simp [select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

omit [DecidableEq I] in

/-- Applying SELECT to `phi0 β φ` gives the frame vector `Vphi0 β P φ`. -/
theorem select_phi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) :
    select P *ᵥ phi0 β φ = Vphi0 β P φ := by
  ext ji
  rcases ji with ⟨j,i⟩
  rw [select_mulVec]
  simp only [phi0, Vphi0, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq J] in

/-- If the squared real amplitudes sum to one, the embedding's Gram matrix is the identity. -/
theorem embedding_gram (β : J → ℝ) (hβ : ∑ j, β j^2=1) :
    (embedding (I := I) β)ᴴ * embedding (I := I) β = 1 := by
  ext x y
  by_cases h : x=y
  · subst y
    have hc : (∑ j, (β j : ℂ)^2)=1 := by exact_mod_cast hβ
    simpa [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      apply_ite, pow_two] using hc
  · simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      apply_ite, h, Ne.symm h]

/-- The entry of SELECT composed with the embedding is the auxiliary amplitude `β j` times the
corresponding entry of `P j`. -/
theorem select_embedding (β : J → ℝ) (P : J → Matrix I I ℂ) :
    select P * embedding (I := I) β = fun ji x => (β ji.1 : ℂ) * P ji.1 ji.2 x := by
  ext ji x
  rcases ji with ⟨j,i⟩
  simp [Matrix.mul_apply, select, embedding, Fintype.sum_prod_type, mul_comm]

/-- Compressing SELECT between the embedding adjoint and the embedding gives the weighted
Hamiltonian `ham β P`. -/
theorem compression (β : J → ℝ) (P : J → Matrix I I ℂ) :
    (embedding (I := I) β)ᴴ * select P * embedding (I := I) β = ham β P := by
  rw [Matrix.mul_assoc, select_embedding]
  ext x y
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    ham, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pow_two, mul_assoc, apply_ite]

omit [DecidableEq I] in

/-- The product of two SELECT matrices is SELECT applied to the branchwise matrix products. -/
theorem select_mul (P Q : J → Matrix I I ℂ) :
    select P * select Q = select (fun j => P j * Q j) := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k
    simp [select, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [select, Matrix.mul_apply, Fintype.sum_prod_type, h]

omit [Fintype J] [Fintype I] in

/-- SELECT applied to identity matrices on every branch is the identity. -/
theorem select_one : select (fun _ : J => (1 : Matrix I I ℂ)) = 1 := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k; simp [select, Matrix.one_apply]
  · simp [select, h]

/-- If every branch matrix squares to the identity, its SELECT matrix also squares to the
identity. -/
theorem select_square (P : J → Matrix I I ℂ) (hP : ∀ j, P j * P j=1) :
    select P * select P = 1 := by
  rw [select_mul]
  simp only [hP]
  exact select_one

omit [Fintype J] [Fintype I] [DecidableEq I] in

/-- If every branch matrix equals its conjugate transpose, the SELECT matrix also equals its
conjugate transpose. -/
theorem select_adjoint (P : J → Matrix I I ℂ) (hP : ∀ j, (P j)ᴴ=P j) :
    (select P)ᴴ=select P := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k
    simpa [select, Matrix.conjTranspose_apply] using congrFun (congrFun (hP j) i) l
  · simp [select, Matrix.conjTranspose_apply, h, Ne.symm h]

/-- The matrix `embedding β * (embedding β)ᴴ` associated with the embedded signal subspace. -/
def signalProjector (β : J → ℝ) : Matrix (J × I) (J × I) ℂ :=
    embedding (I := I) β * (embedding (I := I) β)ᴴ

omit [DecidableEq J] in

/-- For squared amplitudes summing to one, the embedding adjoint sends `phi0 β φ` back to `φ`. -/
theorem embedding_adjoint_phi0 (β : J → ℝ) (hβ : ∑ j, β j^2=1) (φ : State I) :
    (embedding (I := I) β)ᴴ *ᵥ phi0 β φ = φ := by
  rw [← embedding_mulVec, Matrix.mulVec_mulVec, embedding_gram β hβ, Matrix.one_mulVec]

/-- The embedding adjoint sends `Vphi0 β P φ` to the Hamiltonian action `ham β P *ᵥ φ`. -/
theorem embedding_adjoint_Vphi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) :
    (embedding (I := I) β)ᴴ *ᵥ Vphi0 β P φ = ham β P *ᵥ φ := by
  rw [← select_phi0, ← embedding_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    compression]

/-- If the squared amplitudes sum to one and `φ` satisfies the Hamiltonian eigenvector equation
at `E`, the embedding adjoint annihilates `phi1 β P φ E`. -/
theorem embedding_adjoint_phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    (embedding (I := I) β)ᴴ *ᵥ phi1 β P φ E = 0 := by
  change (embedding (I := I) β)ᴴ *ᵥ
    (((Real.sqrt (1-E^2) : ℂ))⁻¹ • (Vphi0 β P φ - (E : ℂ) • phi0 β φ))=0
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
    embedding_adjoint_Vphi0, embedding_adjoint_phi0 β hβ, heig, sub_self, smul_zero]

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
