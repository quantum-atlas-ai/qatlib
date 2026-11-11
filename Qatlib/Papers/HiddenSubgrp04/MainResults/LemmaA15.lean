/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Error from normalizing a nearby vector

This module proves the real inner-product-space estimate `lemma_A15`. A nonzero vector within ε
of a unit vector, for 0 ≤ ε ≤ 1, remains within ε√2 after normalization.

The development follows [Lomont2004].

## Main statements

* `lemma_A15`: If `a` has norm one, `b` is nonzero, and their distance is at most ε with 0 ≤ ε ≤
  1, then the distance from `a` to `b` divided by its norm is at most ε√2.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

/-- If `a` has norm one, `b` is nonzero, and their distance is at most ε with 0 ≤ ε ≤ 1, then
the distance from `a` to `b` divided by its norm is at most ε√2 ([Lemma A.15][Lomont2004]). -/
theorem lemma_A15 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ε : ℝ) (ha : ‖a‖ = 1) (hb : b ≠ 0)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (h : ‖a - b‖ ≤ ε) :
    ‖a - ((‖b‖)⁻¹ : ℝ) • b‖ ≤ ε * Real.sqrt 2 := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let b' : E := (‖b‖⁻¹ : ℝ) • b
  have hb'unit : ‖b'‖ = 1 := by
    dsimp [b']
    exact norm_smul_inv_norm (𝕜 := ℝ) hb
  have hc : 0 ≤ 1 - ε ^ 2 := by nlinarith [sq_nonneg ε, hε1]
  have hnorm_sq : ‖a - b‖ ^ 2 ≤ ε ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg (a - b)) h 2
    simpa using this

  have hinner : 1 + ‖b‖ ^ 2 - ε ^ 2 ≤ 2 * ⟪a, b⟫_ℝ := by
    have hsq := norm_sub_sq_real a b
    rw [ha] at hsq
    nlinarith [hsq, hnorm_sq]

  have hinner_b' : (1 + ‖b‖ ^ 2 - ε ^ 2) / ‖b‖ ≤ 2 * ⟪a, b'⟫_ℝ := by
    have hinner_eq : ⟪a, b'⟫_ℝ = (‖b‖⁻¹) * ⟪a, b⟫_ℝ := by
      dsimp [b']
      rw [real_inner_smul_right]
    rw [hinner_eq, div_le_iff₀ hbpos]
    have hinv : ‖b‖ * ‖b‖⁻¹ = 1 := mul_inv_cancel₀ hbpos.ne'
    nlinarith [hinner, hinv]

  have hsub_sq : ‖a - b'‖ ^ 2 ≤ 2 * ε ^ 2 := by
    have hsq := norm_sub_sq_real a b'
    rw [ha, hb'unit] at hsq
    have hdiv : (1 + ‖b‖ ^ 2 - ε ^ 2) / ‖b‖ = ‖b‖ + (1 - ε ^ 2) / ‖b‖ := by
      field_simp [hbpos.ne']
      ring

    have hAM : 2 * Real.sqrt (1 - ε ^ 2) ≤ ‖b‖ + (1 - ε ^ 2) / ‖b‖ := by
      have hsq' : 0 ≤ (‖b‖ - Real.sqrt (1 - ε ^ 2)) ^ 2 := sq_nonneg _
      have hkey : ‖b‖ + (1 - ε ^ 2) / ‖b‖ - 2 * Real.sqrt (1 - ε ^ 2) =
          (‖b‖ - Real.sqrt (1 - ε ^ 2)) ^ 2 / ‖b‖ := by
        field_simp [hbpos.ne']
        nlinarith [Real.sq_sqrt hc]
      rw [← sub_nonneg, hkey]
      exact div_nonneg hsq' hbpos.le

    have hsqrt_ge : 1 - ε ^ 2 ≤ Real.sqrt (1 - ε ^ 2) := by
      have hle1 : Real.sqrt (1 - ε ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ε])
      have hmul : Real.sqrt (1 - ε ^ 2) * Real.sqrt (1 - ε ^ 2) ≤
          Real.sqrt (1 - ε ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hle1 (Real.sqrt_nonneg _)
      rw [← Real.sq_sqrt hc]
      simpa [pow_two] using hmul
    have hεc : ε ^ 2 = 1 - (1 - ε ^ 2) := by ring
    nlinarith [hsq, hinner_b', hdiv, hAM, hsqrt_ge]
  have hfinal : ‖a - b'‖ ≤ ε * Real.sqrt 2 := by
    calc
      ‖a - b'‖ ≤ Real.sqrt (2 * ε ^ 2) := by
        rw [← Real.sqrt_sq (norm_nonneg _)]
        exact Real.sqrt_le_sqrt hsub_sq
      _ = ε * Real.sqrt 2 := by
        rw [show (2 : ℝ) * ε ^ 2 = ε ^ 2 * 2 by ring]
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0]
  simpa [b'] using hfinal

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
