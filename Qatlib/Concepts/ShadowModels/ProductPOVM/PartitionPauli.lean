/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality

/-!
# Pauli operators on partitioned registers

`partitionRegister` identifies a qubit register with a family of block registers, and
`partitionWord` restricts Pauli words to those blocks. The module constructs partition product
states and proves that Pauli conjugation acts blockwise and preserves their set. See
[XuEtAl2026] for background.

## Main statements

* `pauli_partition_matrix`: a Pauli operator factors over the chosen partition.
* `partitionState_conjugate`: Pauli conjugation of a partition product state is blockwise.
* `partitionStates_pauli_closed`: partition product states are closed under Pauli conjugation.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
variable {J : Type*} [Fintype J] [DecidableEq J] {N : ℕ} (sizes : J → ℕ)

/-- The equivalence between a global qubit register and the family of block registers specified
by `sites`. -/
def partitionRegister (sites : Fin N ≃ Σ j,Fin (sizes j)) : Reg N ≃ (∀ j,Reg (sizes j)) where
  toFun x j k := x (sites.symm ⟨j,k⟩)
  invFun x k := x (sites k).1 (sites k).2
  left_inv x := by ext k;simp
  right_inv x := by
    ext j k
    exact congrArg (fun a : Σ j,Fin (sizes j) => x a.1 a.2) (sites.apply_symm_apply ⟨j,k⟩)

/-- Restrict a global Pauli word to the block indexed by `j` using the site equivalence. -/
def partitionWord (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N) (j : J) : PauliWord (sizes j) :=
  fun k => w (sites.symm ⟨j,k⟩)

omit [DecidableEq J] in

/-- A global Pauli word operator is the product of its block operators, reindexed by
`partitionRegister`. -/
theorem pauli_partition_matrix (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N) :
    pauliWordOp N w=(Matrix.piProd (fun j => pauliWordOp (sizes j) (partitionWord sizes sites w j))).submatrix
      (partitionRegister sizes sites) (partitionRegister sizes sites) := by
  ext x y
  simp only [pauliWordOp_eq,productMatrix,Matrix.piProd,Matrix.submatrix_apply,Matrix.of_apply]
  change (∏ k : Fin N,P1 (w k) (x k) (y k))=
    ∏ j,∏ k : Fin (sizes j),P1 (w (sites.symm ⟨j,k⟩)) (x (sites.symm ⟨j,k⟩)) (y (sites.symm ⟨j,k⟩))
  calc _ = ∏ a : Σ j,Fin (sizes j),P1 (w (sites.symm a)) (x (sites.symm a)) (y (sites.symm a)) :=
           Fintype.prod_equiv sites _ _ (by intro k;simp)
       _ = _ := Fintype.prod_sigma _

/-- The global state obtained by forming the product of the block states and reindexing along
`partitionRegister`. -/
def partitionState (sites : Fin N ≃ Σ j,Fin (sizes j)) (ρ : ∀ j,MState (Reg (sizes j))) : MState (Reg N) :=
  (MState.piProd ρ).relabel (partitionRegister sizes sites)

/-- The set of global states that are products across the specified partition. -/
def partitionStates (sites : Fin N ≃ Σ j,Fin (sizes j)) : Set (MState (Reg N)) :=
  Set.range (partitionState sizes sites)

/-- The set of product states across the specified partition is nonempty. -/
theorem partitionStates_nonempty (sites : Fin N ≃ Σ j,Fin (sizes j)) : (partitionStates sizes sites).Nonempty :=
  ⟨_,fun _ => MState.uniform,rfl⟩

/-- Conjugating a partition product state by a Pauli word equals the product of the
corresponding blockwise Pauli conjugations. -/
theorem partitionState_conjugate (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : ∀ j,MState (Reg (sizes j))) :
    pauliConjugateState N w (partitionState sizes sites ρ)=
      partitionState sizes sites (fun j => pauliConjugateState (sizes j) (partitionWord sizes sites w j) (ρ j)) := by
  apply MState.ext_m
  change pauliWordOp N w*(Matrix.piProd (fun j => (ρ j).m)).submatrix (partitionRegister sizes sites) (partitionRegister sizes sites)*
      (pauliWordOp N w)ᴴ =
    (Matrix.piProd (fun j => pauliWordOp (sizes j) (partitionWord sizes sites w j)*(ρ j).m*
      (pauliWordOp (sizes j) (partitionWord sizes sites w j))ᴴ)).submatrix (partitionRegister sizes sites) (partitionRegister sizes sites)
  rw [pauli_partition_matrix sizes sites,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  congr 1
  change productMatrix _*productMatrix _*(productMatrix _)ᴴ=productMatrix _
  rw [productMatrix_adjoint,productMatrix_mul,productMatrix_mul]

/-- Pauli conjugation preserves the set of states that are products across the specified
partition. -/
theorem partitionStates_pauli_closed (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : MState (Reg N)) (hρ : ρ∈partitionStates sizes sites) :
    pauliConjugateState N w ρ∈partitionStates sizes sites := by
  obtain ⟨ρj,rfl⟩ := hρ
  rw [partitionState_conjugate]
  exact ⟨_,rfl⟩

end Qatlib.Concepts.ShadowModels.ProductPOVM
