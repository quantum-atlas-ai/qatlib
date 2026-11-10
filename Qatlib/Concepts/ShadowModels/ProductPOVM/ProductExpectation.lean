/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PartitionPauli
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators RealInnerProductSpace
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
variable {J : Type*} [Fintype J] [DecidableEq J] {N : ℕ} (sizes : J → ℕ)

theorem trace_submatrix_partition (sites : Fin N ≃ Σ j,Fin (sizes j))
    (A : Matrix (∀ j,Reg (sizes j)) (∀ j,Reg (sizes j)) ℂ) :
    (A.submatrix (partitionRegister sizes sites) (partitionRegister sizes sites)).trace=A.trace :=
  Fintype.sum_equiv (partitionRegister sizes sites) _ _ (by intro x;rfl)

theorem partition_expectation (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : ∀ j,MState (Reg (sizes j))) :
    (partitionState sizes sites ρ).exp_val (pauliObservable N w)=
      ∏ j,(ρ j).exp_val (pauliObservable (sizes j) (partitionWord sizes sites w j)) := by
  have hc {d : Type} [Fintype d] (A B : HermitianMat d ℂ) :
      Complex.ofReal ⟪A,B⟫=(A.mat*B.mat).trace := HermitianMat.inner_eq_trace_mul A B
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_prod,MState.exp_val,hc]
  change ((Matrix.piProd (fun j => (ρ j).m)).submatrix (partitionRegister sizes sites) (partitionRegister sizes sites)*pauliWordOp N w).trace=
    ∏ j,((ρ j).m*pauliWordOp (sizes j) (partitionWord sizes sites w j)).trace
  rw [pauli_partition_matrix sizes sites,Matrix.submatrix_mul_equiv,trace_submatrix_partition]
  change (productMatrix (fun j => (ρ j).m)*productMatrix (fun j => pauliWordOp (sizes j) (partitionWord sizes sites w j))).trace=_
  rw [productMatrix_mul,productMatrix_trace]

theorem partition_expectation_sq (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : ∀ j,MState (Reg (sizes j))) :
    ((partitionState sizes sites ρ).exp_val (pauliObservable N w))^2=
      ∏ j,((ρ j).exp_val (pauliObservable (sizes j) (partitionWord sizes sites w j)))^2 := by
  rw [partition_expectation,Finset.prod_pow]

end Qatlib.Concepts.ShadowModels.ProductPOVM
