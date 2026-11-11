/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

/-!
# Affine and quadratic Boolean coefficient arrays

This module defines affine and quadratic coefficient arrays with an optional slot for constants,
together with their linear evaluation maps at Boolean assignments. The operation `multiply`
compiles a product of affine expressions into quadratic coefficients, providing algebraic
infrastructure for formulations such as [SuksmonoMinato2019].

## Main statements

* `quadraticEval_multiply`: Evaluate an affine outer product.
* `affineEval_variable`: Evaluate a variable coefficient vector.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.QuboForms
open Qatlib.Foundations.BooleanEnergy.HadamardGram

/-- Real affine coefficient vectors indexed by optional variables, with `none` representing the
constant term. -/
abbrev Affine (V : Type*) := Option V → ℝ

/-- Real quadratic coefficient arrays indexed by pairs of optional variables. -/
abbrev Quadratic (V : Type*) := (Option V × Option V) → ℝ

/-- Evaluate an optional variable slot as one for `none` and as the real Boolean bit value for
`some v`. -/
def slot {V : Type*} (x : V → Bool) : Option V → ℝ
  | none => 1
  | some v => bit (x v)

/-- The real-linear evaluation map for affine coefficients at a Boolean assignment. -/
def affineEval {V : Type*} [Fintype V] (x : V → Bool) : Affine V →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i * slot x i
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ i, (c*a i)*slot x i) = c*(∑ i, a i*slot x i)
    simp only [mul_assoc,Finset.mul_sum]

/-- The real-linear evaluation map for quadratic coefficients at a Boolean assignment. -/
def quadraticEval {V : Type*} [Fintype V] (x : V → Bool) : Quadratic V →ₗ[ℝ] ℝ where
  toFun a := ∑ ij, a ij * slot x ij.1 * slot x ij.2
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by
    change (∑ ij, (c*a ij)*slot x ij.1*slot x ij.2) =
      c*(∑ ij, a ij*slot x ij.1*slot x ij.2)
    simp only [mul_assoc,Finset.mul_sum]

/-- The affine coefficient vector supported with value one at the chosen optional variable slot. -/
def atom {V : Type*} [DecidableEq V] (i : Option V) : Affine V := Pi.single i 1

/-- Evaluating an affine atom gives the value of its slot. -/
theorem affineEval_atom {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (i : Option V) : affineEval x (atom i) = slot x i := by
  cases i <;> simp [affineEval,atom,Pi.single_apply]

/-- The outer product of two affine coefficient vectors, viewed as a quadratic coefficient
array. -/
def multiply {V : Type*} (a b : Affine V) : Quadratic V := fun ij => a ij.1 * b ij.2

/-- Evaluating the outer product of affine coefficients gives the product of their affine
evaluations. -/
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

/-- The affine coefficient vector for a single Boolean variable. -/
def coordinate {V : Type*} [DecidableEq V] (v : V) : Affine V := atom (some v)

/-- The affine coefficient vector for the constant function one. -/
def one {V : Type*} [DecidableEq V] : Affine V := atom none

/-- Evaluating a coordinate vector gives the real bit value of that variable. -/
theorem affineEval_variable {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (v : V) : affineEval x (coordinate v) = bit (x v) :=
  affineEval_atom x (some v)

/-- Evaluating the constant affine coefficient vector gives one. -/
theorem affineEval_one {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) : affineEval x (one : Affine V) = 1 := affineEval_atom x none

end Qatlib.Foundations.BooleanEnergy.QuboForms
