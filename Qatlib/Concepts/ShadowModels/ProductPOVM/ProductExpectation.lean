/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PartitionPauli

/-!
# Pauli expectations across a register partition

For a product of mixed states on disjoint register blocks, the expectation of a
Pauli word factors into the product of the corresponding block expectations.
The proof transports traces through the register equivalence and uses tensor
product multiplication and trace identities. Squaring gives the analogous
factorization of squared expectations.

This algebra supports local measurement and classical-shadow models
[HuangKuengPreskill2020]. Tensor-product state semantics are described in
[Nielsen & Chuang, composite systems][NielsenChuang2010].
-/
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

/-- Reindexing both matrix indices along `partitionRegister` preserves the trace. -/
theorem trace_submatrix_partition (sites : Fin N ≃ Σ j,Fin (sizes j))
    (A : Matrix (∀ j,Reg (sizes j)) (∀ j,Reg (sizes j)) ℂ) :
    (A.submatrix (partitionRegister sizes sites) (partitionRegister sizes sites)).trace=A.trace :=
  Fintype.sum_equiv (partitionRegister sizes sites) _ _ (by intro x;rfl)

/-- Pauli expectations factor over product-state register blocks. This is a
tensor-product identity used in the setting of
[Huang, Kueng & Preskill, classical shadows][HuangKuengPreskill2020]. -/
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

/-- The squared expectation of a Pauli word in a partition product state factors as the product
of the squared block expectations, as used in the product characterization of [XuEtAl2026]. -/
theorem partition_expectation_sq (sites : Fin N ≃ Σ j,Fin (sizes j)) (w : PauliWord N)
    (ρ : ∀ j,MState (Reg (sizes j))) :
    ((partitionState sizes sites ρ).exp_val (pauliObservable N w))^2=
      ∏ j,((ρ j).exp_val (pauliObservable (sizes j) (partitionWord sizes sites w j)))^2 := by
  rw [partition_expectation,Finset.prod_pow]

end Qatlib.Concepts.ShadowModels.ProductPOVM
