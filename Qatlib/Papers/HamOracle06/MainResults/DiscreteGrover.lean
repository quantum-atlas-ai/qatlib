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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
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
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Discrete Grover rotation and rounded query time

This module defines the rotation parameter `discreteBetaMagnitude`, the real step count
`discreteGroverSteps`, and the ceiling-rounded time `discreteGroverTime`. It proves a
squared-cosine recursion, the target identity for the real step count, and bounds placing the
rounded time within one step duration of its real-valued counterpart. See [Mochon2007] for the
Hamiltonian oracle formulation.

## Main statements

* `discreteGrover_zeroError_ratio`: For N > 1 and a positive arcsine of the rotation parameter,
  the squared cosine after the real step count equals 1 / N.
* `discreteGroverTime_spec`: For Δ > 0 and a nonnegative real step count, the rounded query time
  lies between Δ times that count and that value plus Δ, with a strict upper bound.
* `discreteGroverTime_minimal`: For Δ > 0, every natural m below the ceiling of the real step
  count satisfies mΔ < `discreteGroverSteps N Δ` · Δ.

## References

* [Mochon, 2007][Mochon2007]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamOracle06.MainResults

/-- The scalar rotation parameter 2 sin(πΔ / 2)√(N − 1) / N. -/
def discreteBetaMagnitude (N Δ : ℝ) : ℝ :=
  2 * Real.sin (Real.pi * Δ / 2) * Real.sqrt (N - 1) / N

/-- The real step count arccos(1 / √N) divided by arcsin(`discreteBetaMagnitude N Δ`). -/
def discreteGroverSteps (N Δ : ℝ) : ℝ :=
  Real.arccos (1 / Real.sqrt N) / Real.arcsin (discreteBetaMagnitude N Δ)

/-- The step duration Δ multiplied by the natural-number ceiling of `discreteGroverSteps N Δ`. -/
def discreteGroverTime (N Δ : ℝ) : ℝ :=
  Δ * (Nat.ceil (discreteGroverSteps N Δ) : ℝ)

/-- For N > 1 and 0 ≤ Δ ≤ 2, `discreteBetaMagnitude N Δ` is nonnegative. -/
theorem discreteBetaMagnitude_nonneg (N Δ : ℝ) (hN : 1 < N)
    (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2) : 0 ≤ discreteBetaMagnitude N Δ := by
  unfold discreteBetaMagnitude
  have hN0 : 0 < N := by linarith
  have hsin : 0 ≤ Real.sin (Real.pi * Δ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have : 0 ≤ Real.pi * Δ / 2 := by positivity
      exact this
    · nlinarith [Real.pi_pos]
  have hsqrt : 0 ≤ Real.sqrt (N - 1) := Real.sqrt_nonneg _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsin) hsqrt) hN0.le

/-- For N > 1 and 0 < Δ < 2, `discreteBetaMagnitude N Δ` is strictly positive. -/
theorem discreteBetaMagnitude_pos (N Δ : ℝ) (hN : 1 < N)
    (hΔ0 : 0 < Δ) (hΔ2 : Δ < 2) : 0 < discreteBetaMagnitude N Δ := by
  unfold discreteBetaMagnitude
  have hN0 : 0 < N := by linarith
  have hsin : 0 < Real.sin (Real.pi * Δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : 0 < Real.pi * Δ / 2 := by positivity
      exact this
    · nlinarith [Real.pi_pos]
  have hsqrt : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  exact div_pos (mul_pos (mul_pos (by norm_num) hsin) hsqrt) hN0

/-- For N > 1 and 0 < Δ < 2, the real discrete Grover step count is nonnegative. -/
theorem discreteGroverSteps_nonneg (N Δ : ℝ) (hN : 1 < N)
    (hΔ0 : 0 < Δ) (hΔ2 : Δ < 2) : 0 ≤ discreteGroverSteps N Δ := by
  unfold discreteGroverSteps
  have harccos : 0 ≤ Real.arccos (1 / Real.sqrt N) := Real.arccos_nonneg _
  have harcsin : 0 < Real.arcsin (discreteBetaMagnitude N Δ) :=
    Real.arcsin_pos.mpr (discreteBetaMagnitude_pos N Δ hN hΔ0 hΔ2)
  exact div_nonneg harccos harcsin.le

/-- Under the stated first-quadrant bounds on β and u, the squared cosine of u + arcsin β
satisfies the recursion expressed using nonnegative square roots. -/
theorem discreteGrover_recursion {β u : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u + Real.arcsin β ≤ Real.pi / 2) :
    Real.cos (u + Real.arcsin β) ^ 2 =
      (Real.sqrt (1 - β ^ 2) * Real.sqrt (Real.cos u ^ 2) -
        β * Real.sqrt (1 - Real.cos u ^ 2)) ^ 2 := by
  have hsβ : 0 ≤ Real.arcsin β := Real.arcsin_nonneg.mpr hβ0
  have huπ : u ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two β, Real.pi_pos]
  have hsin : Real.sqrt (1 - Real.cos u ^ 2) = Real.sin u := by
    have h : 1 - Real.cos u ^ 2 = Real.sin u ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq u]
    rw [h, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hu0 huπ)]
  have hcos : Real.sqrt (Real.cos u ^ 2) = Real.cos u := by
    rw [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) (by linarith))]
  rw [hsin, hcos]
  calc
    Real.cos (u + Real.arcsin β) ^ 2
        = (Real.cos u * Real.cos (Real.arcsin β) -
            Real.sin u * Real.sin (Real.arcsin β)) ^ 2 := by
          rw [Real.cos_add]
    _ = (Real.sqrt (1 - β ^ 2) * Real.cos u - β * Real.sin u) ^ 2 := by
          rw [Real.cos_arcsin, Real.sin_arcsin (by linarith) hβ1]; ring

/-- For N > 1 and a positive arcsine of the rotation parameter, the squared cosine after the
real step count equals 1 / N. See [Mochon2007]. -/
theorem discreteGrover_zeroError_ratio (N Δ : ℝ) (hN : 1 < N)
    (hβ : 0 < Real.arcsin (discreteBetaMagnitude N Δ)) :
    Real.cos (Real.arcsin (discreteBetaMagnitude N Δ) *
      discreteGroverSteps N Δ) ^ 2 = 1 / N := by
  have hstep : Real.arcsin (discreteBetaMagnitude N Δ) * discreteGroverSteps N Δ
      = Real.arccos (1 / Real.sqrt N) := by
    unfold discreteGroverSteps
    rw [mul_comm]
    exact div_mul_cancel₀ _ (ne_of_gt hβ)
  rw [hstep]
  have hN0 : 0 < N := by linarith
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hle : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN.le
  have hmem : 1 / Real.sqrt N ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have hnn : 0 ≤ 1 / Real.sqrt N := by positivity
      linarith
    · rw [div_le_iff₀ hsqrtN]
      simpa using hle
  rw [Real.cos_arccos hmem.1 hmem.2, div_pow, one_pow, Real.sq_sqrt hN0.le]

/-- For Δ ≥ 0, the ceiling-rounded query time is at least Δ times the real step count. -/
theorem discreteGroverTime_ge (N Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Δ * discreteGroverSteps N Δ ≤ discreteGroverTime N Δ := by
  unfold discreteGroverTime
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil (discreteGroverSteps N Δ)) hΔ

/-- For Δ > 0 and a nonnegative real step count, the rounded query time is strictly less than Δ
times that count plus Δ. -/
theorem discreteGroverTime_lt (N Δ : ℝ) (hsteps : 0 ≤ discreteGroverSteps N Δ)
    (hΔ : 0 < Δ) :
    discreteGroverTime N Δ < Δ * discreteGroverSteps N Δ + Δ := by
  unfold discreteGroverTime
  have h1 : (Nat.ceil (discreteGroverSteps N Δ) : ℝ) < discreteGroverSteps N Δ + 1 :=
    Nat.ceil_lt_add_one hsteps
  calc
    Δ * (Nat.ceil (discreteGroverSteps N Δ) : ℝ)
        < Δ * (discreteGroverSteps N Δ + 1) := mul_lt_mul_of_pos_left h1 hΔ
    _ = Δ * discreteGroverSteps N Δ + Δ := by ring

/-- For Δ > 0 and a nonnegative real step count, the rounded query time lies between Δ times
that count and that value plus Δ, with a strict upper bound. See [Mochon2007]. -/
theorem discreteGroverTime_spec (N Δ : ℝ) (hsteps : 0 ≤ discreteGroverSteps N Δ)
    (hΔ : 0 < Δ) :
    Δ * discreteGroverSteps N Δ ≤ discreteGroverTime N Δ ∧
      discreteGroverTime N Δ < Δ * discreteGroverSteps N Δ + Δ :=
  ⟨discreteGroverTime_ge N Δ hΔ.le, discreteGroverTime_lt N Δ hsteps hΔ⟩

/-- For Δ > 0, every natural m below the ceiling of the real step count satisfies mΔ <
`discreteGroverSteps N Δ` · Δ. See [Mochon2007]. -/
theorem discreteGroverTime_minimal (N Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ)
    (hm : m < Nat.ceil (discreteGroverSteps N Δ)) :
    (m : ℝ) * Δ < discreteGroverSteps N Δ * Δ := by
  have h := Nat.lt_ceil.mp hm
  nlinarith

/-- At step duration 1, the rotation parameter equals 2√(N − 1) / N. See [Mochon2007]. -/
theorem discreteBetaMagnitude_one (N : ℝ) :
    discreteBetaMagnitude N 1 = 2 * Real.sqrt (N - 1) / N := by
  unfold discreteBetaMagnitude
  rw [show Real.pi * 1 / 2 = Real.pi / 2 by ring, Real.sin_pi_div_two]
  ring

end Qatlib.Papers.HamOracle06.MainResults
