/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {X : Type*} [Fintype X] {I J K : X → Type*}

def tupleMatrix (A : ∀ x,Matrix (I x) (J x) ℂ) : Matrix (∀ x,I x) (∀ x,J x) ℂ :=
  fun i j => ∏ x,A x (i x) (j x)

theorem tupleMatrix_mul [∀ x,Fintype (J x)]
    (A : ∀ x,Matrix (I x) (J x) ℂ) (B : ∀ x,Matrix (J x) (K x) ℂ) :
    tupleMatrix A*tupleMatrix B=tupleMatrix (fun x => A x*B x) := by
  ext u v
  change (∑ y : ∀ x,J x,(∏ x,A x (u x) (y x))*(∏ x,B x (y x) (v x)))=
    ∏ x,∑ j : J x,A x (u x) j*B x j (v x)
  calc
    _ = ∑ y : ∀ x,J x,∏ x,A x (u x) (y x)*B x (y x) (v x) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.prod_mul_distrib.symm
    _ = _ := (Fintype.prod_sum (fun (x : X) (j : J x) => A x (u x) j*B x j (v x))).symm

theorem tupleMatrix_one : tupleMatrix (fun x => (1 : Matrix (I x) (I x) ℂ))=1 := by
  ext u v
  by_cases huv : u=v
  · subst v
    simp [tupleMatrix]
  · have h : ∃ x,u x ≠ v x := by
      by_contra hn
      push Not at hn
      exact huv (funext hn)
    obtain ⟨x,hx⟩ := h
    simp only [tupleMatrix,Matrix.one_apply,if_neg huv]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

theorem tupleMatrix_adjoint (A : ∀ x,Matrix (I x) (J x) ℂ) :
    (tupleMatrix A)ᴴ=tupleMatrix (fun x => (A x)ᴴ) := by
  ext i j
  simp [tupleMatrix,Matrix.conjTranspose_apply]

theorem tupleMatrix_isometry [∀ x,Fintype (I x)]
    (A : ∀ x,Matrix (I x) (J x) ℂ) (hA : ∀ x,(A x)ᴴ*A x=1) :
    (tupleMatrix A)ᴴ*tupleMatrix A=1 := by
  rw [tupleMatrix_adjoint,tupleMatrix_mul]
  have he : (fun x => (A x)ᴴ*A x)=fun x => (1 : Matrix (J x) (J x) ℂ) := funext hA
  rw [he,tupleMatrix_one]

theorem tupleMatrix_product_apply [∀ x,Fintype (J x)]
    (A : ∀ x,Matrix (I x) (J x) ℂ) (v : ∀ x,J x → ℂ) (u : ∀ x,I x) :
    (tupleMatrix A*ᵥ (fun y => ∏ x,v x (y x))) u=∏ x,(A x*ᵥ v x) (u x) := by
  change (∑ y : ∀ x,J x,(∏ x,A x (u x) (y x))*(∏ x,v x (y x)))=
    ∏ x,∑ j : J x,A x (u x) j*v x j
  calc
    _ = ∑ y : ∀ x,J x,∏ x,A x (u x) (y x)*v x (y x) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.prod_mul_distrib.symm
    _ = _ := (Fintype.prod_sum (fun (x : X) (j : J x) => A x (u x) j*v x j)).symm
end Qatlib.Foundations.MatrixAlgebra.TupleMatrices
