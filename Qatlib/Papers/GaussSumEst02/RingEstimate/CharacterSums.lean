/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.DirichletPhase

/-!
# Dirichlet-character orthogonality

This module characterizes triviality of `DirichletChar` through its Mathlib multiplicative
character. It evaluates complete character sums, giving the totient for trivial characters and
zero for nontrivial characters, and applies this at zero Gauss-sum frequency. See
[VanDamSeroussi2002].

## Main statements

* `dirichlet_sum_eq_zero_of_nontrivial`: The sum of a nontrivial Dirichlet character over all
  residues is zero.
* `dirichlet_sum_eq_totient_of_trivial`: The sum of a trivial Dirichlet character over all
  residues equals Euler's totient of the modulus.
* `ringGaussSum_trivial_zero_index`: At zero frequency, a ring Gauss sum for a trivial Dirichlet
  character equals Euler's totient of the modulus.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.RingEstimate

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- A Dirichlet character is trivial when it equals one at every unit residue. -/
def IsTrivialChar {n : ℕ} (χ : DirichletChar n) : Prop :=
  ∀ x : ZMod n, IsUnit x → χ.toFun x = 1

/-- Triviality of a Dirichlet character is equivalent to its associated Mathlib multiplicative
character being one. -/
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

/-- The sum of a nontrivial Dirichlet character over all residues is zero [VanDamSeroussi2002]. -/
theorem dirichlet_sum_eq_zero_of_nontrivial {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (h : ¬ IsTrivialChar χ) : (∑ x : ZMod n, χ.toFun x) = 0 := by
  exact _root_.MulChar.sum_eq_zero_of_ne_one
    (χ := toMulChar χ) (fun h1 => h ((isTrivial_iff_toMulChar_eq_one χ).mpr h1))

/-- The sum of a trivial Dirichlet character over all residues equals Euler's totient of the
modulus [VanDamSeroussi2002]. -/
theorem dirichlet_sum_eq_totient_of_trivial {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (h : IsTrivialChar χ) :
    (∑ x : ZMod n, χ.toFun x) = Nat.totient n := by
  have h1 : toMulChar χ = 1 := (isTrivial_iff_toMulChar_eq_one χ).mp h
  have hsum : (∑ x : ZMod n, χ.toFun x) = Fintype.card (ZMod n)ˣ := by
    have := _root_.MulChar.sum_one_eq_card_units (R := ZMod n) (R' := ℂ)
    rw [← h1] at this
    simpa [toMulChar_apply] using this
  rw [hsum, ZMod.card_units_eq_totient]

/-- Complete Dirichlet-character sums equal the totient in the trivial case and zero in the
nontrivial case. -/
theorem dirichlet_sum_cases {n : ℕ} [NeZero n] (χ : DirichletChar n) :
    (IsTrivialChar χ → (∑ x : ZMod n, χ.toFun x) = Nat.totient n) ∧
    (¬ IsTrivialChar χ → (∑ x : ZMod n, χ.toFun x) = 0) :=
  ⟨dirichlet_sum_eq_totient_of_trivial χ, dirichlet_sum_eq_zero_of_nontrivial χ⟩

/-- At zero frequency, a ring Gauss sum for a trivial Dirichlet character equals Euler's totient
of the modulus [VanDamSeroussi2002]. -/
theorem ringGaussSum_trivial_zero_index {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) (h : IsTrivialChar χ) :
    ringGaussSum χ e 0 = Nat.totient n := by
  rw [ringGaussSum]
  simp only [zero_mul, e.map_zero', mul_one]
  exact dirichlet_sum_eq_totient_of_trivial χ h

end Qatlib.Papers.GaussSumEst02.RingEstimate
