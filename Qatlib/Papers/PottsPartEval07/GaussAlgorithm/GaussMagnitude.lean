/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
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
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Nontrivial.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.GaussAlgorithm

open scoped BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

noncomputable def gaussSumAt (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (β : F) : ℂ :=
  _root_.gaussSum χ (ψ.mulShift β)

theorem gaussSumAt_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (β : F) :
    gaussSumAt χ ψ β = ∑ x : F, χ x * ψ (β * x) := by
  unfold gaussSumAt
  rw [_root_.gaussSum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [AddChar.mulShift_apply]

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

theorem gaussSumAt_norm_eq_sqrt (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (β : F) (hβ : β ≠ 0) :
    ‖gaussSumAt χ ψ β‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hshift : (ψ.mulShift β).IsPrimitive := by
    intro a ha
    rw [AddChar.mulShift_mulShift]
    exact hψ (mul_ne_zero hβ ha)
  exact gaussSum_norm_eq_sqrt χ hχ (ψ.mulShift β) hshift

theorem kickback_eigenvalue_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (β : F) (hβ : β ≠ 0) (hQ : 0 < Fintype.card F) :
    ‖gaussSumAt χ ψ β / Complex.ofReal (Real.sqrt (Fintype.card F : ℝ))‖ = 1 := by
  have hmod := gaussSumAt_norm_eq_sqrt χ hχ ψ hψ β hβ
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast hQ
  rw [norm_div, hmod, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  field_simp

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
