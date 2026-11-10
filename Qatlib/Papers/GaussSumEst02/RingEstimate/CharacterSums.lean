/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.DirichletPhase
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.RingEstimate

open Qatlib.Papers.GaussSumEst02.MainResults.Source

def IsTrivialChar {n : ℕ} (χ : DirichletChar n) : Prop :=
  ∀ x : ZMod n, IsUnit x → χ.toFun x = 1

theorem isTrivial_iff_toMulChar_eq_one {n : ℕ} (χ : DirichletChar n) :
    IsTrivialChar χ ↔ toMulChar χ = 1 := by
  constructor
  · intro h
    refine _root_.MulChar.ext' fun x => ?_
    by_cases hx : IsUnit x
    · rw [toMulChar_apply, h x hx, _root_.MulChar.one_apply hx]
    · rw [toMulChar_apply, χ.map_zero_of_not_unit x hx,
        _root_.MulChar.map_nonunit (1 : _root_.MulChar (ZMod n) ℂ) hx]
  · intro h x hx
    have hx' := _root_.MulChar.ext_iff.mp h hx.unit
    rw [toMulChar_apply,
      _root_.MulChar.one_apply (x := (↑hx.unit : ZMod n)) hx.unit.isUnit] at hx'
    rw [← hx.unit_spec]
    exact hx'

theorem dirichlet_sum_eq_zero_of_nontrivial {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (h : ¬ IsTrivialChar χ) : (∑ x : ZMod n, χ.toFun x) = 0 := by
  exact _root_.MulChar.sum_eq_zero_of_ne_one
    (χ := toMulChar χ) (fun h1 => h ((isTrivial_iff_toMulChar_eq_one χ).mpr h1))

theorem dirichlet_sum_eq_totient_of_trivial {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (h : IsTrivialChar χ) :
    (∑ x : ZMod n, χ.toFun x) = Nat.totient n := by
  have h1 : toMulChar χ = 1 := (isTrivial_iff_toMulChar_eq_one χ).mp h
  have hsum : (∑ x : ZMod n, χ.toFun x) = Fintype.card (ZMod n)ˣ := by
    have := _root_.MulChar.sum_one_eq_card_units (R := ZMod n) (R' := ℂ)
    rw [← h1] at this
    simpa [toMulChar_apply] using this
  rw [hsum, ZMod.card_units_eq_totient]

theorem dirichlet_sum_cases {n : ℕ} [NeZero n] (χ : DirichletChar n) :
    (IsTrivialChar χ → (∑ x : ZMod n, χ.toFun x) = Nat.totient n) ∧
    (¬ IsTrivialChar χ → (∑ x : ZMod n, χ.toFun x) = 0) :=
  ⟨dirichlet_sum_eq_totient_of_trivial χ, dirichlet_sum_eq_zero_of_nontrivial χ⟩

theorem ringGaussSum_trivial_zero_index {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (h : IsTrivialChar χ) :
    ringGaussSum χ e 0 = Nat.totient n := by
  rw [ringGaussSum]
  simp only [zero_mul, e.map_zero', mul_one]
  exact dirichlet_sum_eq_totient_of_trivial χ h

end Qatlib.Papers.GaussSumEst02.RingEstimate
