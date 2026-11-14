/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Scalar resource comparisons for spectral measurement

This module defines scalar cost expressions for Trotter steps, Trotter rotations, and the
spectral measurement resources discussed in [PoulinEtAl2018]. It proves comparisons under
explicit size and precision inequalities.

## Main statements

* `trotterRotations_eq`: expanded Trotter rotation cost.
* `our_rotations_le_trotter`: comparison when `N ≤ n` and `0 < Δ ≤ Real.sqrt n`.
* `our_third_level_le`: upper bound by `n * n / Δ`.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralMeas17.CostCompare

/-- The scalar Trotter step cost `Real.sqrt n / Δ ^ 2`. -/
def trotterSteps (n Δ : ℝ) : ℝ := Real.sqrt n / Δ ^ 2

/-- The scalar Trotter rotation cost `n * trotterSteps n Δ`. -/
def trotterRotations (n Δ : ℝ) : ℝ := n * trotterSteps n Δ

/-- The scalar Trotter rotation cost equals `n * Real.sqrt n / Δ ^ 2`. -/
theorem trotterRotations_eq (n Δ : ℝ) :
    trotterRotations n Δ = n * Real.sqrt n / Δ ^ 2 := by
  unfold trotterRotations trotterSteps
  ring

/-- The scalar spectral measurement rotation cost `N / Δ`. -/
def ourRotations (N Δ : ℝ) : ℝ := N / Δ

/-- The scalar spectral measurement third-level cost `n * N / Δ`. -/
def ourThirdLevel (n N Δ : ℝ) : ℝ := n * N / Δ

/-- For nonnegative `n` and `N` with `N ≤ n` and `0 < Δ ≤ Real.sqrt n`, the spectral measurement
rotation cost is at most the Trotter rotation cost in the scalar comparison of
[PoulinEtAl2018]. -/
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

/-- For nonnegative `n`, `N ≤ n`, and positive `Δ`, the scalar third-level cost is at most `n *
n / Δ` [PoulinEtAl2018]. -/
theorem our_third_level_le (n N Δ : ℝ) (hn : 0 ≤ n) (hNn : N ≤ n) (hΔ : 0 < Δ) :
    ourThirdLevel n N Δ ≤ n * n / Δ := by
  unfold ourThirdLevel
  rw [div_le_div_iff₀ hΔ hΔ]
  have h1 : n * N ≤ n * n := mul_le_mul_of_nonneg_left hNn hn
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right h1 (le_of_lt hΔ)

end Qatlib.Papers.SpectralMeas17.CostCompare
