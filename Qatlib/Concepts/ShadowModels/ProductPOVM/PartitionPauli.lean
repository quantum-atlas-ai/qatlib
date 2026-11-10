/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality
set_option warningAsError false
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

def partitionRegister (sites : Fin N ≃ Σ j,Fin (sizes j)) : Reg N ≃ (∀ j,Reg (sizes j)) where
  toFun x j k := x (sites.symm ⟨j,k⟩)
  invFun x k := x (sites k).1 (sites k).2
  left_inv x := by ext k;simp
  right_inv x := by
    ext j k
    exact congrArg (fun a : Σ j,Fin (sizes j) => x a.1 a.2) (sites.apply_symm_apply ⟨j,k⟩)

def partitionWord (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N) (j : J) : PauliWord (sizes j) :=
  fun k => w (sites.symm ⟨j,k⟩)

omit [DecidableEq J] in

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

def partitionState (sites : Fin N ≃ Σ j,Fin (sizes j)) (ρ : ∀ j,MState (Reg (sizes j))) : MState (Reg N) :=
  (MState.piProd ρ).relabel (partitionRegister sizes sites)

def partitionStates (sites : Fin N ≃ Σ j,Fin (sizes j)) : Set (MState (Reg N)) :=
  Set.range (partitionState sizes sites)

theorem partitionStates_nonempty (sites : Fin N ≃ Σ j,Fin (sizes j)) : (partitionStates sizes sites).Nonempty :=
  ⟨_,fun _ => MState.uniform,rfl⟩

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

theorem partitionStates_pauli_closed (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : MState (Reg N)) (hρ : ρ∈partitionStates sizes sites) :
    pauliConjugateState N w ρ∈partitionStates sizes sites := by
  obtain ⟨ρj,rfl⟩ := hρ
  rw [partitionState_conjugate]
  exact ⟨_,rfl⟩

end Qatlib.Concepts.ShadowModels.ProductPOVM
