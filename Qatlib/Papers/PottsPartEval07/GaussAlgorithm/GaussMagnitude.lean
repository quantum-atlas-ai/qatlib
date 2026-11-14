/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Magnitudes of Gauss-sum kickback factors

Using Mathlib's Gauss sums, `gaussSumAt` expresses scaling of the additive character by a field
element. A nontrivial multiplicative character and a primitive additive character give Gauss-sum
magnitude equal to the square root of the field cardinality, so the corresponding normalized
kickback factor has norm one [GeraciLidar2008].

## Main statements

* `gaussSumAt_norm_eq_sqrt`: A nonzero additive scaling preserves the square-root magnitude.
* `kickback_eigenvalue_norm`: The normalized Gauss sum has unit norm.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.GaussAlgorithm

open scoped BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

/-- The Gauss sum formed using the additive character `ψ` shifted multiplicatively by `β`. -/
noncomputable def gaussSumAt (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (β : F) : ℂ :=
  _root_.gaussSum χ (ψ.mulShift β)

/-- The shifted Gauss sum equals the finite sum of `χ x * ψ (β * x)`. -/
theorem gaussSumAt_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (β : F) :
    gaussSumAt χ ψ β = ∑ x : F, χ x * ψ (β * x) := by
  unfold gaussSumAt
  rw [_root_.gaussSum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [AddChar.mulShift_apply]

/-- A Gauss sum for a nontrivial multiplicative character and a primitive additive character has
norm equal to the square root of the field cardinality [GeraciLidar2008]. -/
theorem gaussSum_norm_eq_sqrt (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) :
    ‖_root_.gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by

  have hmul : _root_.gaussSum χ ψ * conj (_root_.gaussSum χ ψ) = (Fintype.card F : ℂ) := by
    have h1 : star (_root_.gaussSum χ ψ) = conj (_root_.gaussSum χ ψ) := rfl
    rw [← h1, star_gaussSum_eq]
    exact gaussSum_mul_gaussSum_eq_card hχ hψ

  have hsq : ‖_root_.gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have h := hmul
    rw [Complex.mul_conj'] at h
    exact_mod_cast h
  calc ‖_root_.gaussSum χ ψ‖ = Real.sqrt (‖_root_.gaussSum χ ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (Fintype.card F : ℝ) := by rw [hsq]

/-- Scaling a primitive additive character by a nonzero parameter gives a Gauss sum of
square-root magnitude. -/
theorem gaussSumAt_norm_eq_sqrt (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (β : F) (hβ : β ≠ 0) :
    ‖gaussSumAt χ ψ β‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hshift : (ψ.mulShift β).IsPrimitive := by
    intro a ha
    rw [AddChar.mulShift_mulShift]
    exact hψ (mul_ne_zero hβ ha)
  exact gaussSum_norm_eq_sqrt χ hχ (ψ.mulShift β) hshift

/-- Dividing the scaled Gauss sum by the square root of the field cardinality gives a complex
number of norm one [GeraciLidar2008]. -/
theorem kickback_eigenvalue_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (β : F) (hβ : β ≠ 0) (hQ : 0 < Fintype.card F) :
    ‖gaussSumAt χ ψ β / Complex.ofReal (Real.sqrt (Fintype.card F : ℝ))‖ = 1 := by
  have hmod := gaussSumAt_norm_eq_sqrt χ hχ ψ hψ β hβ
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast hQ
  rw [norm_div, hmod, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  field_simp

/-- The character-square correction of the Fourier-type amplitude equals the character amplitude
times `gaussSumAt χ ψ β`. -/
theorem kickback_normalised_amplitude (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (β : F)
    (y : F) (hy : y ≠ 0) :
    χ y ^ 2 * ((∑ x : F, χ x * ψ (β * x * y)))
      = χ y * gaussSumAt χ ψ β := by
  have hχy : χ y ≠ 0 := by
    have hu : IsUnit y := isUnit_iff_ne_zero.mpr hy
    have hcoe : χ y = (χ.toUnitHom hu.unit : ℂ) := by
      rw [MulChar.coe_toUnitHom, hu.unit_spec]
    rw [hcoe]
    exact Units.ne_zero _
  have hshift : (∑ x : F, χ x * ψ (β * x * y)) = _root_.gaussSum χ (ψ.mulShift (β * y)) := by
    rw [_root_.gaussSum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [AddChar.mulShift_apply]
    congr 2
    ring
  have hrel : _root_.gaussSum χ (ψ.mulShift (β * y)) = (χ y)⁻¹ * gaussSumAt χ ψ β := by
    have hunit := gaussSum_mulShift_eq χ (ψ.mulShift β) (Units.mk0 y hy)
    rw [AddChar.mulShift_mulShift] at hunit
    rw [MulChar.inv_apply_eq_inv'] at hunit
    simp only [Units.val_mk0] at hunit
    simpa [gaussSumAt] using hunit
  rw [hshift, hrel]
  have hcancel : χ y ^ 2 * (χ y)⁻¹ = χ y := by
    rw [sq, mul_assoc, mul_inv_cancel₀ hχy, mul_one]
  calc χ y ^ 2 * ((χ y)⁻¹ * gaussSumAt χ ψ β)
      = (χ y ^ 2 * (χ y)⁻¹) * gaussSumAt χ ψ β := by ring
    _ = χ y * gaussSumAt χ ψ β := by rw [hcancel]

end Qatlib.Papers.PottsPartEval07.GaussAlgorithm
