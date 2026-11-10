/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.Polynomial.TensorGradient
import Qatlib.Papers.QGradient20.DressedUpdate.Encoding
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QGradient20.Polynomial

structure Term (p : ℕ) (I : Type*) where
  coefficient : ℝ
  left : TensorIndex p (Option I)
  right : TensorIndex p (Option I)

def termMatrix {p : ℕ} {I : Type} [DecidableEq I] (t : Term p I) :
    Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ :=
  fun u v => (if u=t.left then if v=t.right then t.coefficient else 0 else 0) +
    (if u=t.right then if v=t.left then t.coefficient else 0 else 0)

theorem termMatrix_symmetric {p : ℕ} {I : Type} [DecidableEq I] (t : Term p I) :
    (termMatrix t).IsSymm := by
  apply Matrix.IsSymm.ext
  intro u v
  simp only [termMatrix]
  split_ifs <;> ring

theorem objective_termMatrix {p : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (t : Term p I) (x : Option I → ℝ) :
    objective (termMatrix t) x = t.coefficient * amplitude x t.left * amplitude x t.right := by
  classical
  simp [objective,termMatrix,add_mul,ite_mul,Finset.sum_add_distrib]
  ring

def coefficientMatrix {p : ℕ} {I T : Type} [Fintype T] [DecidableEq I]
    (terms : T → Term p I) : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ :=
  ∑ t, termMatrix (terms t)

theorem coefficientMatrix_symmetric {p : ℕ} {I T : Type} [Fintype T] [DecidableEq I]
    (terms : T → Term p I) : (coefficientMatrix terms).IsSymm := by
  apply Matrix.IsSymm.ext
  intro u v
  simp only [coefficientMatrix, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun B => B u v) (termMatrix_symmetric (terms t)).eq

theorem coefficientMatrix_represents {p : ℕ} {I T : Type} [Fintype T] [Fintype I] [DecidableEq I]
    (terms : T → Term p I) (x : I → ℝ) :
    objective (coefficientMatrix terms) (DressedUpdate.homogeneousInput x) =
      ∑ t, (terms t).coefficient * amplitude (DressedUpdate.homogeneousInput x) (terms t).left *
        amplitude (DressedUpdate.homogeneousInput x) (terms t).right := by
  unfold coefficientMatrix objective
  simp only [Matrix.sum_apply,Finset.sum_mul]
  have he (u : TensorIndex p (Option I)) :
      (∑ v, ∑ t, termMatrix (terms t) u v * amplitude (DressedUpdate.homogeneousInput x) u *
        amplitude (DressedUpdate.homogeneousInput x) v) =
      ∑ t, ∑ v, termMatrix (terms t) u v * amplitude (DressedUpdate.homogeneousInput x) u *
        amplitude (DressedUpdate.homogeneousInput x) v := Finset.sum_comm
  simp only [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact objective_termMatrix (terms t) _

end Qatlib.Papers.QGradient20.Polynomial
