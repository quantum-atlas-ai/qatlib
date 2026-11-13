/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore

/-!
# Dirichlet characters and ring Gauss sums

This module defines `DirichletChar` on residue rings and the associated `ringGaussSum`.
Unit-frequency scaling transfers an assumed norm at one to other unit frequencies, and character
multiplication is an isometry on states supported on units. See [VanDamSeroussi2002].

## Main statements

* `ringGaussSum_scale`: At a unit frequency `β`, the ring Gauss sum equals the base sum at one
  times the character value at the inverse unit.
* `ringGaussSum_norm`: If the base ring Gauss sum has norm `√n`, every unit-frequency sum has
  norm `√n`.
* `dirichlet_phaseChange_isometry`: Multiplication by a Dirichlet character preserves total
  squared norm for a function vanishing on nonunits.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- A complex character on `ZMod n` that equals one at one, vanishes on nonunits, and is
multiplicative with unit norm on units. -/
structure DirichletChar (n : ℕ) where
  toFun : ZMod n → ℂ
  map_one' : toFun 1 = 1
  map_zero_of_not_unit : ∀ x : ZMod n, ¬ IsUnit x → toFun x = 0
  map_mul_of_unit : ∀ x y : ZMod n, IsUnit x → IsUnit y → toFun (x * y) = toFun x * toFun y
  norm_eq_one : ∀ x : ZMod n, IsUnit x → ‖toFun x‖ = 1

/-- The sum of `χ(x) * e(βx)` over all residues modulo `n`. -/
def ringGaussSum {n : ℕ} [NeZero n] (χ : DirichletChar n) (e : AddChar (ZMod n)) (β : ZMod n) : ℂ :=
  ∑ x : ZMod n, χ.toFun x * e.toFun (β * x)

/-- The value of a Dirichlet character at a unit is nonzero. -/
theorem DirichletChar.toFun_ne_zero {n : ℕ} (χ : DirichletChar n) {x : ZMod n}
    (hx : IsUnit x) : χ.toFun x ≠ 0 := by
  intro h
  have := χ.norm_eq_one x hx
  rw [h, norm_zero] at this
  norm_num at this

/-- At a unit frequency `β`, the ring Gauss sum equals the base sum at one times the character
value at the inverse unit. -/
theorem ringGaussSum_scale {n : ℕ} [NeZero n] (χ : DirichletChar n) (e : AddChar (ZMod n))
    {β : ZMod n} (hβ : IsUnit β) :
    ringGaussSum χ e β
      = χ.toFun (↑hβ.unit⁻¹) * ringGaussSum χ e 1 := by
  classical
  have hu : IsUnit (↑hβ.unit⁻¹ : ZMod n) := (hβ.unit⁻¹).isUnit
  have hβu : β * (↑hβ.unit⁻¹ : ZMod n) = 1 := hβ.mul_val_inv
  rw [ringGaussSum, ringGaussSum, Finset.mul_sum]
  have hstep : (∑ z : ZMod n, χ.toFun ((↑hβ.unit⁻¹ : ZMod n) * z)
        * e.toFun (β * ((↑hβ.unit⁻¹ : ZMod n) * z)))
      = ∑ x : ZMod n, χ.toFun x * e.toFun (β * x) := by
    simpa using Equiv.sum_comp (hβ.unit⁻¹).mulLeft
      (fun x : ZMod n => χ.toFun x * e.toFun (β * x))
  rw [← hstep]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : IsUnit z
  · have huz : IsUnit ((↑hβ.unit⁻¹ : ZMod n) * z) := (IsUnit.mul_left_iff hu).mpr hz
    rw [χ.map_mul_of_unit _ _ hu hz,
      show β * ((↑hβ.unit⁻¹ : ZMod n) * z) = z by
        rw [← mul_assoc, hβu, one_mul]]
    simp only [one_mul]
    ring
  · have hnuz : ¬ IsUnit ((↑hβ.unit⁻¹ : ZMod n) * z) := by
      rw [IsUnit.mul_left_iff hu]
      exact hz
    rw [χ.map_zero_of_not_unit _ hnuz, χ.map_zero_of_not_unit _ hz]
    simp only [one_mul]
    ring

/-- If the base ring Gauss sum has norm `√n`, every unit-frequency sum has norm `√n`
[VanDamSeroussi2002]. -/
theorem ringGaussSum_norm {n : ℕ} [NeZero n] (χ : DirichletChar n) (e : AddChar (ZMod n))
    {β : ZMod n} (hβ : IsUnit β) (h1 : ‖ringGaussSum χ e 1‖ = Real.sqrt (n : ℝ)) :
    ‖ringGaussSum χ e β‖ = Real.sqrt (n : ℝ) := by
  rw [ringGaussSum_scale χ e hβ, norm_mul,
    χ.norm_eq_one (↑hβ.unit⁻¹) (hβ.unit⁻¹).isUnit, h1, one_mul]

/-- Multiplication by a Dirichlet character retains exactly the squared-norm contributions from
unit residues. -/
theorem dirichlet_phaseChange_normSq {n : ℕ} [NeZero n] (χ : DirichletChar n) (ψ : ZMod n → ℂ) :
    (∑ x : ZMod n, ‖χ.toFun x * ψ x‖ ^ 2)
      = ∑ x : ZMod n, if IsUnit x then ‖ψ x‖ ^ 2 else 0 := by
  classical
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : IsUnit x
  · rw [if_pos hx, norm_mul, χ.norm_eq_one x hx, one_mul]
  · rw [if_neg hx, χ.map_zero_of_not_unit x hx, zero_mul, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Multiplication by a Dirichlet character preserves total squared norm for a function
vanishing on nonunits [VanDamSeroussi2002]. -/
theorem dirichlet_phaseChange_isometry {n : ℕ} [NeZero n] (χ : DirichletChar n)
    (ψ : ZMod n → ℂ) (hψ : ∀ x : ZMod n, ¬ IsUnit x → ψ x = 0) :
    (∑ x : ZMod n, ‖χ.toFun x * ψ x‖ ^ 2) = ∑ x : ZMod n, ‖ψ x‖ ^ 2 := by
  classical
  rw [dirichlet_phaseChange_normSq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : IsUnit x
  · rw [if_pos hx]
  · rw [if_neg hx, hψ x hx, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end Qatlib.Papers.GaussSumEst02.MainResults.Source
