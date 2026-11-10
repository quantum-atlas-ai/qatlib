/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.QuboForms
open Qatlib.Foundations.BooleanEnergy.HadamardGram

abbrev Affine (V : Type*) := Option V → ℝ

abbrev Quadratic (V : Type*) := (Option V × Option V) → ℝ

def slot {V : Type*} (x : V → Bool) : Option V → ℝ
  | none => 1
  | some v => bit (x v)

def affineEval {V : Type*} [Fintype V] (x : V → Bool) : Affine V →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i * slot x i
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ i, (c*a i)*slot x i) = c*(∑ i, a i*slot x i)
    simp only [mul_assoc,Finset.mul_sum]

def quadraticEval {V : Type*} [Fintype V] (x : V → Bool) : Quadratic V →ₗ[ℝ] ℝ where
  toFun a := ∑ ij, a ij * slot x ij.1 * slot x ij.2
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ ij, (c*a ij)*slot x ij.1*slot x ij.2) =
      c*(∑ ij, a ij*slot x ij.1*slot x ij.2)
    simp only [mul_assoc,Finset.mul_sum]

def atom {V : Type*} [DecidableEq V] (i : Option V) : Affine V := Pi.single i 1

theorem affineEval_atom {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (i : Option V) : affineEval x (atom i) = slot x i := by
  cases i <;> simp [affineEval,atom,Pi.single_apply]

def multiply {V : Type*} (a b : Affine V) : Quadratic V := fun ij => a ij.1 * b ij.2

theorem quadraticEval_multiply {V : Type*} [Fintype V]
    (x : V → Bool) (a b : Affine V) :
    quadraticEval x (multiply a b) = affineEval x a * affineEval x b := by
  change (∑ ij : Option V × Option V, a ij.1*b ij.2*slot x ij.1*slot x ij.2) =
    (∑ i, a i*slot x i)*(∑ j, b j*slot x j)
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def coordinate {V : Type*} [DecidableEq V] (v : V) : Affine V := atom (some v)

def one {V : Type*} [DecidableEq V] : Affine V := atom none

theorem affineEval_variable {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (v : V) : affineEval x (coordinate v) = bit (x v) :=
  affineEval_atom x (some v)

theorem affineEval_one {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) : affineEval x (one : Affine V) = 1 := affineEval_atom x none

end Qatlib.Foundations.BooleanEnergy.QuboForms
