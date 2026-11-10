/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
namespace Qatlib.Concepts.TensorRegisters.RegisterModel.EncodedDiscard
open scoped BigOperators ComplexOrder

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]
variable {n m : ℕ}

def joint (a : A ≃ Fin n) (b : B ≃ Fin m) (M : Matrix (B × A) (B × A) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  M.submatrix (fun i => (b.symm i.2, a.symm i.1))
    (fun i => (b.symm i.2, a.symm i.1))

def retained (a : A ≃ Fin n) (b : B ≃ Fin m) (M : Matrix (B × A) (B × A) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ y : Fin m, joint a b M (i, y) (j, y)

omit [Fintype A] in

theorem retained_apply (a : A ≃ Fin n) (b : B ≃ Fin m)
    (M : Matrix (B × A) (B × A) ℂ) (i j : Fin n) :
    retained a b M i j = ∑ y : B, M (y, a.symm i) (y, a.symm j) := by
  apply Fintype.sum_equiv b.symm
  intro y
  rfl

omit [Fintype A] [Fintype B] in

theorem joint_posSemidef (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef) :
    (joint a b M).PosSemidef :=
  hM.submatrix _

omit [Fintype A] [Fintype B] in

theorem retained_posSemidef (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef) :
    (retained a b M).PosSemidef := by
  have h := Matrix.posSemidef_sum (Finset.univ : Finset (Fin m))
    (fun y _ => (joint_posSemidef a b hM).submatrix (fun i => (i, y)))
  convert h using 1
  ext i j
  simp only [retained, Matrix.sum_apply, Matrix.submatrix_apply]

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

theorem retained_density (a : A ≃ Fin n) (b : B ≃ Fin m)
    {M : Matrix (B × A) (B × A) ℂ} (hM : M.PosSemidef)
    (htrace : Matrix.trace M = 1) :
    (retained a b M).PosSemidef ∧ Matrix.trace (retained a b M) = 1 :=
  ⟨retained_posSemidef a b hM, (retained_trace a b M).trans htrace⟩

end
end Qatlib.Concepts.TensorRegisters.RegisterModel.EncodedDiscard
