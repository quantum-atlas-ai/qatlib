/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-!
# Discarding an encoded environment register

The matrix `joint` reorders and encodes a bipartite register, and `retained` discards its
environment by summing diagonal environment blocks. The reduction preserves positive
semidefiniteness and trace, hence maps density matrices to density matrices. For background, see
[Watrous2018].

## Main statements

* `retained_apply`: entries of the retained matrix as an environment sum.
* `retained_density`: discarding preserves positive semidefiniteness and unit trace.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.TensorRegisters.RegisterModel.EncodedDiscard
open scoped BigOperators ComplexOrder

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]
variable {n m : ℕ}

/-- The joint matrix in encoded coordinates, with the retained `A` register first and the
environment `B` register second. -/
def joint (a : A ≃ Fin n) (b : B ≃ Fin m) (M : Matrix (B × A) (B × A) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  M.submatrix (fun i => (b.symm i.2, a.symm i.1))
    (fun i => (b.symm i.2, a.symm i.1))

/-- The encoded retained-register matrix obtained by summing the diagonal environment blocks of
`joint a b M`. -/
def retained (a : A ≃ Fin n) (b : B ≃ Fin m) (M : Matrix (B × A) (B × A) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ y : Fin m, joint a b M (i, y) (j, y)

omit [Fintype A] in

/-- Entries of `retained a b M` are sums of `M (y, a.symm i) (y, a.symm j)` over environment
labels `y`. -/
theorem retained_apply (a : A ≃ Fin n) (b : B ≃ Fin m)
    (M : Matrix (B × A) (B × A) ℂ) (i j : Fin n) :
    retained a b M i j = ∑ y : B, M (y, a.symm i) (y, a.symm j) := by
  apply Fintype.sum_equiv b.symm
  intro y
  rfl

omit [Fintype A] [Fintype B] in

/-- Reordering and encoding the joint register preserves positive semidefiniteness. -/
theorem joint_posSemidef (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef) :
    (joint a b M).PosSemidef :=
  hM.submatrix _

omit [Fintype A] [Fintype B] in

/-- Discarding the encoded environment preserves positive semidefiniteness. -/
theorem retained_posSemidef (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef) :
    (retained a b M).PosSemidef := by
  have h := Matrix.posSemidef_sum (Finset.univ : Finset (Fin m))
    (fun y _ => (joint_posSemidef a b hM).submatrix (fun i => (i, y)))
  convert h using 1
  ext i j
  simp only [retained, Matrix.sum_apply, Matrix.submatrix_apply]

/-- The trace of the retained matrix equals the trace of the original joint matrix. -/
theorem retained_trace (a : A ≃ Fin n) (b : B ≃ Fin m)
    (M : Matrix (B × A) (B × A) ℂ) :
    Matrix.trace (retained a b M) = Matrix.trace M := by
  change (∑ i : Fin n, retained a b M i i) = ∑ i : B × A, M i i
  simp only [retained_apply]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Fintype.sum_equiv a.symm
  intro i
  rfl

/-- A positive semidefinite joint matrix of trace one yields a positive semidefinite retained
matrix of trace one. -/
theorem retained_density (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef)
    (htrace : Matrix.trace M = 1) :
    (retained a b M).PosSemidef ∧ Matrix.trace (retained a b M) = 1 :=
  ⟨retained_posSemidef a b hM, (retained_trace a b M).trans htrace⟩

end
end Qatlib.Concepts.TensorRegisters.RegisterModel.EncodedDiscard
