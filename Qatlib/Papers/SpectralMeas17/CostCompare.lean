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
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralMeas17.CostCompare

def trotterSteps (n Δ : ℝ) : ℝ := Real.sqrt n / Δ ^ 2

def trotterRotations (n Δ : ℝ) : ℝ := n * trotterSteps n Δ

theorem trotterRotations_eq (n Δ : ℝ) :
    trotterRotations n Δ = n * Real.sqrt n / Δ ^ 2 := by
  unfold trotterRotations trotterSteps
  ring

def ourRotations (N Δ : ℝ) : ℝ := N / Δ

def ourThirdLevel (n N Δ : ℝ) : ℝ := n * N / Δ

theorem our_rotations_le_trotter (n N Δ : ℝ) (hn : 0 ≤ n) (hN : 0 ≤ N) (hNn : N ≤ n)
    (hΔ : 0 < Δ) (hΔn : Δ ≤ Real.sqrt n) :
    ourRotations N Δ ≤ trotterRotations n Δ := by
  rw [trotterRotations_eq]
  unfold ourRotations
  rw [div_le_div_iff₀ hΔ (pow_pos hΔ 2)]
  have h1 : N * Δ ≤ n * Real.sqrt n := by
    have a : N * Δ ≤ n * Δ := mul_le_mul_of_nonneg_right hNn (le_of_lt hΔ)
    have b : n * Δ ≤ n * Real.sqrt n := mul_le_mul_of_nonneg_left hΔn hn
    have hNΔ : 0 ≤ N * Δ := mul_nonneg hN (le_of_lt hΔ)
    linarith
  have h2 : N * Δ * Δ ≤ n * Real.sqrt n * Δ :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt hΔ)
  simpa [pow_two, mul_assoc] using h2

theorem our_third_level_le (n N Δ : ℝ) (hn : 0 ≤ n) (hNn : N ≤ n) (hΔ : 0 < Δ) :
    ourThirdLevel n N Δ ≤ n * n / Δ := by
  unfold ourThirdLevel
  rw [div_le_div_iff₀ hΔ hΔ]
  have h1 : n * N ≤ n * n := mul_le_mul_of_nonneg_left hNn hn
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right h1 (le_of_lt hΔ)

end Qatlib.Papers.SpectralMeas17.CostCompare
