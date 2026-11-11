/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Gauss-sum phase kickback identities

The Gauss sum `gaussSum` pairs a multiplicative character with a scaled additive character.
Changing a nonzero additive parameter gives the character factor needed for the coordinate
identities `kickback` and `kickback_normalised`; `characterState` records the unnormalized
character amplitudes [GeraciLidar2008].

## Main statements

* `gaussSum_mul_right`: Rescaling the additive parameter introduces the inverse multiplicative
  character.
* `kickback_normalised`: The normalized character amplitudes satisfy the Gauss-sum kickback
  identity.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.GaussAlgorithm

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The Gauss sum of `χ` and the additive character `e` scaled by the field parameter `β`. -/
noncomputable def gaussSum (χ : MulChar F ℂ) (e : AddChar F ℂ) (β : F) : ℂ :=
  ∑ x : F, χ x * e (β * x)

/-- The unnormalized amplitude function of a multiplicative-character state. -/
noncomputable def characterState (χ : MulChar F ℂ) : F → ℂ := fun x => χ x

/-- A multiplicative character has nonzero value at every nonzero field element. -/
theorem mulChar_apply_ne_zero {χ : MulChar F ℂ} {y : F} (hy : y ≠ 0) : χ y ≠ 0 := by
  have hu : IsUnit y := isUnit_iff_ne_zero.mpr hy
  have hcoe : χ y = (χ.toUnitHom hu.unit : ℂ) := by
    rw [MulChar.coe_toUnitHom, hu.unit_spec]
  rw [hcoe]
  exact Units.ne_zero _

/-- The sum of a nontrivial multiplicative character over the finite field is zero
[GeraciLidar2008]. -/
theorem character_sum_zero {χ : MulChar F ℂ} (hχ : χ ≠ 1) : ∑ x : F, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

/-- Scaling the additive parameter by nonzero `y` multiplies the Gauss sum by the inverse of `χ
y` [GeraciLidar2008]. -/
theorem gaussSum_mul_right (χ : MulChar F ℂ) (e : AddChar F ℂ) (β y : F) (hy : y ≠ 0) :
    gaussSum χ e (β * y) = (χ y)⁻¹ * gaussSum χ e β := by
  have hχy : χ y ≠ 0 := mulChar_apply_ne_zero hy
  unfold gaussSum
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun x _ => y * x) (fun x _ => Finset.mem_univ _)
    (fun x₁ _ x₂ _ h => mul_left_cancel₀ hy h)
    (fun b _ => ⟨y⁻¹ * b, Finset.mem_univ _, by field_simp⟩) ?_
  intro x _
  have hχmul : χ (y * x) = χ y * χ x := map_mul χ y x
  have harg : β * (y * x) = β * y * x := by ring
  rw [hχmul, harg]
  have hsimp : (χ y)⁻¹ * ((χ y * χ x) * e (β * y * x)) = χ x * e (β * y * x) := by
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hχy, one_mul]
  rw [hsimp]

/-- Multiplication by `χ y ^ 2` converts the Fourier-type sum at nonzero `y` into `χ y` times
the Gauss sum [GeraciLidar2008]. -/
theorem kickback (χ : MulChar F ℂ) (e : AddChar F ℂ) (β y : F) (hy : y ≠ 0) :
    χ y ^ 2 * (∑ x : F, χ x * e (β * x * y)) = χ y * gaussSum χ e β := by
  have hχy : χ y ≠ 0 := mulChar_apply_ne_zero hy
  have hstep : (∑ x : F, χ x * e (β * x * y)) = gaussSum χ e (β * y) := by
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    ring
  rw [hstep, gaussSum_mul_right χ e β y hy]
  have hcancel : χ y ^ 2 * (χ y)⁻¹ = χ y := by
    rw [sq, mul_assoc, mul_inv_cancel₀ hχy, mul_one]
  rw [show χ y ^ 2 * ((χ y)⁻¹ * gaussSum χ e β)
        = (χ y ^ 2 * (χ y)⁻¹) * gaussSum χ e β by ring, hcancel]

/-- The kickback identity with normalization factor `N⁻¹` has scalar factor `gaussSum χ e β *
N⁻¹` [GeraciLidar2008]. -/
theorem kickback_normalised (χ : MulChar F ℂ) (e : AddChar F ℂ) (β y : F) (hy : y ≠ 0)
    (N : ℂ) (hN : N ≠ 0) :
    χ y ^ 2 * ((N⁻¹) * ∑ x : F, χ x * e (β * x * y))
      = (gaussSum χ e β * N⁻¹) * (χ y) := by
  have hχy : χ y ≠ 0 := mulChar_apply_ne_zero hy
  have hk := kickback χ e β y hy
  calc χ y ^ 2 * (N⁻¹ * ∑ x : F, χ x * e (β * x * y))
      = N⁻¹ * (χ y ^ 2 * ∑ x : F, χ x * e (β * x * y)) := by ring
    _ = N⁻¹ * (χ y * gaussSum χ e β) := by rw [hk]
    _ = (gaussSum χ e β * N⁻¹) * χ y := by ring

end Qatlib.Papers.PottsPartEval07.GaussAlgorithm
