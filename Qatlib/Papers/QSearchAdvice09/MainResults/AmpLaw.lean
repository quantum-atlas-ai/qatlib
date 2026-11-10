/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Iterate
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
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

open scoped BigOperators

noncomputable section

open Finset Real

namespace Qatlib.Papers.QSearchAdvice09.MainResults

abbrev AmpPair : Type := ℝ × ℝ

def reflMarked (v : AmpPair) : AmpPair := (-v.1, v.2)

def reflAdvice (θ : ℝ) (v : AmpPair) : AmpPair :=
  (v.1 - 2 * (v.1 * sin θ + v.2 * cos θ) * sin θ,
    v.2 - 2 * (v.1 * sin θ + v.2 * cos θ) * cos θ)

def groverStep (θ : ℝ) (v : AmpPair) : AmpPair :=
  let w := reflAdvice θ (reflMarked v)
  (-w.1, -w.2)

theorem groverStep_apply (θ a b : ℝ) :
    groverStep θ (a, b) =
      (cos (2 * θ) * a + sin (2 * θ) * b, -sin (2 * θ) * a + cos (2 * θ) * b) := by
  ext
  · simp only [groverStep, reflAdvice, reflMarked, Prod.fst, Prod.snd,
      Real.sin_two_mul, Real.cos_two_mul]
    have key : a * sin θ ^ 2 + a * cos θ ^ 2 = a := by
      linear_combination a * (Real.sin_sq_add_cos_sq θ)
    nlinarith [key]
  · simp only [groverStep, reflAdvice, reflMarked, Prod.fst, Prod.snd,
      Real.sin_two_mul, Real.cos_two_mul]
    have key : b * sin θ ^ 2 + b * cos θ ^ 2 = b := by
      linear_combination b * (Real.sin_sq_add_cos_sq θ)
    nlinarith [key]

theorem groverStep_norm (θ a b : ℝ) :
    (groverStep θ (a, b)).1 ^ 2 + (groverStep θ (a, b)).2 ^ 2 = a ^ 2 + b ^ 2 := by
  rw [groverStep_apply]
  have h : sin (2 * θ) ^ 2 + cos (2 * θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * θ)
  nlinarith [h]

theorem groverStep_sincos (θ φ : ℝ) :
    groverStep θ (sin φ, cos φ) = (sin (φ + 2 * θ), cos (φ + 2 * θ)) := by
  rw [groverStep_apply, Real.sin_add, Real.cos_add]
  ring

theorem groverStep_iterate (θ : ℝ) (k : ℕ) :
    (groverStep θ)^[k] (sin θ, cos θ) =
      (sin ((2 * (k : ℝ) + 1) * θ), cos ((2 * (k : ℝ) + 1) * θ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, groverStep_sincos]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

theorem ampAmplify_success (θ : ℝ) (k : ℕ) :
    ((groverStep θ)^[k] (sin θ, cos θ)).1 ^ 2 =
      sin ((2 * (k : ℝ) + 1) * θ) ^ 2 := by
  rw [groverStep_iterate]

theorem ampAmplify_success_sqrt (p : ℝ) (hp : 0 ≤ p) (k : ℕ) :
    ((groverStep (arcsin (sqrt p)))^[k]
        (sin (arcsin (sqrt p)), cos (arcsin (sqrt p)))).1 ^ 2 =
      sin ((2 * (k : ℝ) + 1) * arcsin (sqrt p)) ^ 2 := by
  rw [groverStep_iterate]

theorem two_sin_two_mul_sum_cos (θ : ℝ) (m : ℕ) :
    2 * sin (2 * θ) * (∑ r ∈ range m, cos ((4 * (r : ℝ) + 2) * θ)) =
      sin (4 * (m : ℝ) * θ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    have h : 2 * sin (2 * θ) * cos ((4 * (m : ℝ) + 2) * θ) =
        sin ((4 * (m : ℝ) + 2) * θ + 2 * θ) - sin ((4 * (m : ℝ) + 2) * θ - 2 * θ) := by
      rw [Real.sin_add, Real.sin_sub]
      ring
    rw [h]
    have h1 : (4 * (m : ℝ) + 2) * θ + 2 * θ = 4 * ((m : ℝ) + 1) * θ := by ring
    have h2 : (4 * (m : ℝ) + 2) * θ - 2 * θ = 4 * (m : ℝ) * θ := by ring
    rw [h1, h2]
    push_cast
    ring_nf

theorem sum_sin_sq_eq (θ : ℝ) (m : ℕ) :
    ∑ r ∈ range m, sin ((2 * (r : ℝ) + 1) * θ) ^ 2 =
      (m : ℝ) / 2 - (1 / 2) * ∑ r ∈ range m, cos ((4 * (r : ℝ) + 2) * θ) := by
  have hterm : ∀ r : ℕ, sin ((2 * (r : ℝ) + 1) * θ) ^ 2 =
      (1 / 2 : ℝ) - (1 / 2) * cos ((4 * (r : ℝ) + 2) * θ) := by
    intro r
    have h2 : (4 * (r : ℝ) + 2) * θ = 2 * ((2 * (r : ℝ) + 1) * θ) := by ring
    rw [h2, Real.cos_two_mul]
    have h3 : sin ((2 * (r : ℝ) + 1) * θ) ^ 2 + cos ((2 * (r : ℝ) + 1) * θ) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    nlinarith [h3]
  calc ∑ r ∈ range m, sin ((2 * (r : ℝ) + 1) * θ) ^ 2
      = ∑ r ∈ range m, ((1 / 2 : ℝ) - (1 / 2) * cos ((4 * (r : ℝ) + 2) * θ)) := by
        exact sum_congr rfl fun r _ => hterm r
    _ = (m : ℝ) / 2 - (1 / 2) * ∑ r ∈ range m, cos ((4 * (r : ℝ) + 2) * θ) := by
        rw [sum_sub_distrib, sum_const, card_range, ← mul_sum]
        simp only [nsmul_eq_mul]
        ring

theorem average_amp_success (θ : ℝ) (m : ℕ) (hm : 0 < m) (h : sin θ * cos θ ≠ 0) :
    (1 / (m : ℝ)) * (∑ r ∈ range m, sin ((2 * (r : ℝ) + 1) * θ) ^ 2) =
      1 / 2 - sin (4 * (m : ℝ) * θ) / (8 * (m : ℝ) * sin θ * cos θ) := by
  have hm' : ((m : ℝ)) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hm
  have hsin : sin θ ≠ 0 := fun hz => h (by rw [hz, zero_mul])
  have hcosθ : cos θ ≠ 0 := fun hz => h (by rw [hz, mul_zero])
  have h2θ : sin (2 * θ) ≠ 0 := by
    rw [Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hsin) hcosθ
  have hcos : ∑ r ∈ range m, cos ((4 * (r : ℝ) + 2) * θ) =
      sin (4 * (m : ℝ) * θ) / (2 * sin (2 * θ)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero h2θ), mul_comm]
    exact two_sin_two_mul_sum_cos θ m
  rw [sum_sin_sq_eq, hcos, Real.sin_two_mul]
  field_simp
  ring

theorem average_amp_success_ge_quarter (θ : ℝ) (m : ℕ) (hm : 0 < m)
    (hpos : 0 < sin θ * cos θ) (h : 1 ≤ 2 * (m : ℝ) * (sin θ * cos θ)) :
    1 / 4 ≤ (1 / (m : ℝ)) * (∑ r ∈ range m, sin ((2 * (r : ℝ) + 1) * θ) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : sin θ * cos θ ≠ 0 := ne_of_gt hpos
  rw [average_amp_success θ m hm hne]
  have hden : 0 < 8 * (m : ℝ) * sin θ * cos θ := by
    have : 0 < 8 * (m : ℝ) * (sin θ * cos θ) := by positivity
    calc 0 < 8 * (m : ℝ) * (sin θ * cos θ) := this
      _ = 8 * (m : ℝ) * sin θ * cos θ := by ring
  have hsin : |sin (4 * (m : ℝ) * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hle : sin (4 * (m : ℝ) * θ) / (8 * (m : ℝ) * sin θ * cos θ) ≤
      1 / (8 * (m : ℝ) * sin θ * cos θ) := by
    rw [div_le_div_iff_of_pos_right hden]
    exact (le_abs_self _).trans hsin
  have hquarter : 1 / (8 * (m : ℝ) * sin θ * cos θ) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ 8 * (m : ℝ) * sin θ * cos θ := by
      nlinarith [h]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h4
  linarith [hle, hquarter]

end Qatlib.Papers.QSearchAdvice09.MainResults
