/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.RingEstimate

open Qatlib.Papers.GaussSumEst02.MainResults.Source

def toMulChar {n : ℕ} (χ : DirichletChar n) : _root_.MulChar (ZMod n) ℂ where
  toFun := χ.toFun
  map_one' := χ.map_one'
  map_mul' := fun x y => by
    by_cases hxy : IsUnit (x * y)
    · obtain ⟨hx, hy⟩ := IsUnit.mul_iff.mp hxy
      exact χ.map_mul_of_unit x y hx hy
    · by_cases hx : IsUnit x
      · have hy : ¬ IsUnit y := fun hy => hxy (hx.mul hy)
        rw [χ.map_zero_of_not_unit _ hxy, χ.map_zero_of_not_unit _ hy, mul_zero]
      · rw [χ.map_zero_of_not_unit _ hxy, χ.map_zero_of_not_unit _ hx, zero_mul]
  map_nonunit' := fun x hx => χ.map_zero_of_not_unit x hx

def toAddChar {n : ℕ} (e : AddChar (ZMod n)) : _root_.AddChar (ZMod n) ℂ where
  toFun := e.toFun
  map_zero_eq_one' := e.map_zero'
  map_add_eq_mul' := e.map_add'

@[simp] lemma toMulChar_apply {n : ℕ} (χ : DirichletChar n) (x : ZMod n) :
    toMulChar χ x = χ.toFun x := rfl

@[simp] lemma toAddChar_apply {n : ℕ} (e : AddChar (ZMod n)) (x : ZMod n) :
    toAddChar e x = e.toFun x := rfl

theorem ringGaussSum_eq_gaussSum {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (β : ZMod n) :
    ringGaussSum χ e β = _root_.gaussSum (toMulChar χ) ((toAddChar e).mulShift β) := by
  rw [ringGaussSum, _root_.gaussSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [_root_.AddChar.mulShift_apply]

theorem ringGaussSum_one_eq_gaussSum {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) :
    ringGaussSum χ e 1 = _root_.gaussSum (toMulChar χ) (toAddChar e) := by
  rw [ringGaussSum_eq_gaussSum, _root_.AddChar.mulShift_one]

theorem ringGaussSum_zero_of_not_unit {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (hχ : DirichletCharacter.IsPrimitive (toMulChar χ)) {β : ZMod n}
    (hβ : ¬ IsUnit β) :
    ringGaussSum χ e β = 0 := by
  rw [ringGaussSum_eq_gaussSum]
  rw [gaussSum_mulShift_of_isPrimitive (χ := toMulChar χ) (e := toAddChar e) hχ β]
  rw [_root_.MulChar.map_nonunit _ hβ, zero_mul]

theorem ringGaussSum_primitive_scale {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (hχ : DirichletCharacter.IsPrimitive (toMulChar χ)) (β : ZMod n) :
    ringGaussSum χ e β
      = (toMulChar χ)⁻¹ β * ringGaussSum χ e 1 := by
  rw [ringGaussSum_eq_gaussSum, ringGaussSum_one_eq_gaussSum]
  exact gaussSum_mulShift_of_isPrimitive (χ := toMulChar χ) (e := toAddChar e) hχ β

theorem DirichletChar.inv_apply {n : ℕ} (χ : DirichletChar n) {x : ZMod n}
    (hx : IsUnit x) : χ.toFun (↑hx.unit⁻¹) = (χ.toFun x)⁻¹ := by
  have hval : (↑hx.unit : ZMod n) = x := hx.unit_spec
  have hprod : χ.toFun (↑hx.unit⁻¹) * χ.toFun (↑hx.unit) = 1 := by
    rw [← χ.map_mul_of_unit _ _ (hx.unit⁻¹).isUnit hx.unit.isUnit, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, χ.map_one']
  rw [hval] at hprod
  exact eq_inv_of_mul_eq_one_left hprod

theorem primitive_fourier_phase_eigen {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (hχ : DirichletCharacter.IsPrimitive (toMulChar χ)) (y : ZMod n) :
    χ.toFun y ^ 2 * ringGaussSum χ e y = ringGaussSum χ e 1 * χ.toFun y := by
  by_cases hy : IsUnit y
  · rw [ringGaussSum_scale χ e hy]
    have hχy : χ.toFun y ≠ 0 := χ.toFun_ne_zero hy
    rw [DirichletChar.inv_apply χ hy]
    field_simp
  · have hzero : ringGaussSum χ e y = 0 := ringGaussSum_zero_of_not_unit χ e hχ hy
    rw [hzero, χ.map_zero_of_not_unit y hy]
    ring

theorem algorithm2_primitive_eigenphase {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (hχ : DirichletCharacter.IsPrimitive (toMulChar χ)) :
    (∀ β : ZMod n, ¬ IsUnit β → ringGaussSum χ e β = 0) ∧
    (∀ β : ZMod n,
      ringGaussSum χ e β = (toMulChar χ)⁻¹ β * ringGaussSum χ e 1) ∧
    (∀ y : ZMod n,
      χ.toFun y ^ 2 * ringGaussSum χ e y = ringGaussSum χ e 1 * χ.toFun y) :=
  ⟨fun _ hβ => ringGaussSum_zero_of_not_unit χ e hχ hβ,
   fun β => ringGaussSum_primitive_scale χ e hχ β,
   fun y => primitive_fourier_phase_eigen χ e hχ y⟩

end Qatlib.Papers.GaussSumEst02.RingEstimate
