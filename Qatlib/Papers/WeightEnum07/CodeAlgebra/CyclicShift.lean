/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.Submodule.Bilinear

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.CodeAlgebra

open scoped BigOperators

variable (R : Type*) [CommRing R]

def shift (n : ℕ) : (ZMod n → R) →ₗ[R] (ZMod n → R) where
  toFun v := fun i => v (i - 1)
  map_add' x y := by
    funext i
    rfl
  map_smul' r x := by
    funext i
    rfl

lemma shift_iter_apply (n : ℕ) (v : ZMod n → R) :
    ∀ (k : ℕ) (i : ZMod n), ((shift R n)^[k]) v i = v (i - (k : ZMod n)) := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply']
      change ((shift R n)^[k]) v (i - 1) = v (i - ((k + 1 : ℕ) : ZMod n))
      rw [ih (i - 1)]
      congr 1
      push_cast
      abel

theorem shift_pow_n (n : ℕ) : (shift R n) ^ n = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  rw [Module.End.pow_apply, shift_iter_apply, ZMod.natCast_self, sub_zero]
  simp

def polyShift (n : ℕ) (p : Polynomial R) : Module.End R (ZMod n → R) :=
  Polynomial.aeval (shift R n) p

lemma polyShift_X (n : ℕ) : polyShift R n (Polynomial.X : Polynomial R) = shift R n := by
  rw [polyShift, Polynomial.aeval_X]

theorem polyShift_X_pow_sub_one (n : ℕ) :
    polyShift R n ((Polynomial.X : Polynomial R) ^ n - 1) = 0 := by
  rw [polyShift, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one,
    shift_pow_n, sub_self]

lemma shift_pow_mem {n : ℕ} {C : Submodule R (ZMod n → R)}
    (hC : ∀ v ∈ C, shift R n v ∈ C) :
    ∀ (k : ℕ) {v : ZMod n → R}, v ∈ C → ((shift R n) ^ k) v ∈ C := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih (hC v hv)

theorem isCyclic_iff_polyShift (n : ℕ) (C : Submodule R (ZMod n → R)) :
    (∀ v ∈ C, shift R n v ∈ C) ↔
      (∀ (p : Polynomial R) (v : ZMod n → R), v ∈ C → polyShift R n p v ∈ C) := by
  constructor
  · intro hC p v hv
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [polyShift, map_add]
        exact Submodule.add_mem _ hp hq
    | monomial k a =>
        rw [polyShift, Polynomial.aeval_monomial]
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ a (shift_pow_mem R hC k hv)
  · intro hC v hv
    have h := hC (Polynomial.X : Polynomial R) v hv
    simpa [polyShift_X] using h

end Qatlib.Papers.WeightEnum07.CodeAlgebra
