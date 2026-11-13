/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.GroverArbAmp98.MainResults.Dynamics

/-!
# Optimal real times in the Grover cosine model

This module studies the real-valued cosine model `successAt` for the success oscillation in
[BihamEtAl1999]. It proves that the specified real measurement times attain `Pmax`, records a
reciprocal identity for positive success values, and identifies the rotation angle with the one
in `Dynamics`.

Under `1 ≤ r` and `2*r ≤ r+m`, `iterations_big_O` gives an explicit upper bound for the first
real-time expression with square-root dependence on `(r+m)/r` and a factor depending on the
phase.

## Main statements

* `optimal_time_achieves_Pmax`: exact attainment at the specified real times.
* `iterations_big_O`: an explicit square-root upper bound on the real-time expression.

## References

* [Biham et al., 1999][BihamEtAl1999]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GroverArbAmp98.MainResults.MeasurementTime

/-- The cosine success model `Pav - ΔP * cos θ`. -/
def successAt (Pav ΔP θ : ℝ) : ℝ := Pav - ΔP * Real.cos θ

/-- The envelope value `Pav + ΔP` for the cosine success model. -/
def Pmax (Pav ΔP : ℝ) : ℝ := Pav + ΔP

/-- For nonnegative `ΔP`, every phase of the cosine success model is bounded above by `Pmax Pav
ΔP`. -/
lemma success_le_Pmax (Pav ΔP θ : ℝ) (hΔ0 : 0 ≤ ΔP) :
    successAt Pav ΔP θ ≤ Pmax Pav ΔP := by
  unfold successAt Pmax
  have h : -ΔP ≤ ΔP * Real.cos θ := by
    have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hΔ0
    simpa using this
  linarith

/-- For nonzero `ω`, evaluating the cosine model at real time `((j + 1/2) * π - φ) / ω` gives
`Pmax Pav ΔP` [BihamEtAl1999]. -/
theorem optimal_time_achieves_Pmax (Pav ΔP φ ω : ℝ) (j : ℕ) (hω : ω ≠ 0) :
    successAt Pav ΔP (2 * (ω * ((((j : ℝ) + 1 / 2) * Real.pi - φ) / ω) + φ))
      = Pmax Pav ΔP := by
  unfold successAt Pmax
  have hθ : 2 * (ω * ((((j : ℝ) + 1 / 2) * Real.pi - φ) / ω) + φ)
      = (2 * (j : ℝ) + 1) * Real.pi := by
    field_simp
    try ring
  have hcos : Real.cos ((2 * (j : ℝ) + 1) * Real.pi) = -1 := by
    rw [show (2 * (j : ℝ) + 1) * Real.pi = (j : ℝ) * (2 * Real.pi) + Real.pi by ring]
    exact Real.cos_nat_mul_two_pi_add_pi j
  rw [hθ, hcos]
  ring

/-- For positive `Pmax`, multiplying its reciprocal by `Pmax` gives one [BihamEtAl1999]. -/
theorem inverse_repetitions_arithmetic (Pmax : ℝ) (hpos : 0 < Pmax) :
    (1 / Pmax) * Pmax = 1 := by
  field_simp

/-- The real angle `arccos (1 - 2r/(r+m))` used in the measurement-time expression. -/
def omegaR (r m : ℕ) : ℝ :=
  Real.arccos (1 - 2 * (r : ℝ) / ((r + m : ℕ) : ℝ))

/-- The measurement-time rotation angle equals the angle defined in `Dynamics`. -/
lemma omegaR_eq_omega (r m : ℕ) : omegaR r m = Dynamics.omega r m := rfl

/-- For positive total size, the sine of the measurement-time rotation angle is `2√(r*m)/(r+m)`. -/
lemma sin_omegaR (r m : ℕ) (hN : 0 < r + m) :
    Real.sin (omegaR r m)
      = 2 * Real.sqrt ((r : ℝ) * (m : ℝ)) / ((r + m : ℕ) : ℝ) := by
  rw [omegaR_eq_omega]
  exact Dynamics.omega_sin r m hN

/-- For `1 ≤ r` and `2*r ≤ r+m`, the real-time expression `(π/2 - φ) / omegaR r m` is at most
`(π/2 + |φ|) * √((r+m)/r) / √2` [BihamEtAl1999]. -/
theorem iterations_big_O (r m : ℕ) (φ : ℝ) (hr : 1 ≤ r) (hrm : 2 * r ≤ r + m) :
    (Real.pi / 2 - φ) / omegaR r m ≤
      (Real.pi / 2 + |φ|) * Real.sqrt (((r + m : ℕ) : ℝ) / (r : ℝ)) / Real.sqrt 2 := by
  set N : ℝ := ((r + m : ℕ) : ℝ) with hNdef
  have hrm' : r ≤ m := by omega
  have hNpos : 0 < N := by
    rw [hNdef]
    exact_mod_cast (by omega : 0 < r + m)
  have hRpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hRm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm'
  have htwoRpos : 0 < 2 * (r : ℝ) / N := by positivity

  have hsin := sin_omegaR r m (by omega)
  have hN2m : N ≤ 2 * (m : ℝ) := by
    rw [hNdef]
    push_cast
    linarith
  have hinner : 2 * (r : ℝ) / N ≤ 4 * (r : ℝ) * (m : ℝ) / N ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : 2 * (r : ℝ) * N * N ≤ 2 * (r : ℝ) * N * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hN2m (by positivity)
    nlinarith [hkey]
  have hsq : Real.sqrt (4 * (r : ℝ) * (m : ℝ) / N ^ 2)
      = 2 * Real.sqrt ((r : ℝ) * (m : ℝ)) / N := by
    rw [Real.sqrt_div (x := 4 * (r : ℝ) * (m : ℝ)) (by positivity) (N ^ 2),
      Real.sqrt_sq (le_of_lt hNpos)]
    rw [show (4 : ℝ) * (r : ℝ) * (m : ℝ) = 4 * ((r : ℝ) * (m : ℝ)) by ring]
    rw [Real.sqrt_mul (x := (4 : ℝ)) (by norm_num) ((r : ℝ) * (m : ℝ))]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hbound : Real.sqrt (2 * (r : ℝ) / N) ≤ Real.sin (omegaR r m) := by
    rw [hsin, ← hsq]
    exact Real.sqrt_le_sqrt hinner

  have hω0 : 0 ≤ omegaR r m := by
    unfold omegaR
    exact Real.arccos_nonneg _
  have hboundω : Real.sqrt (2 * (r : ℝ) / N) ≤ omegaR r m :=
    le_trans hbound (Real.sin_le hω0)
  have hωpos : 0 < omegaR r m :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr htwoRpos) hboundω

  have hinv1 : 1 / omegaR r m ≤ 1 / Real.sqrt (2 * (r : ℝ) / N) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr htwoRpos) hboundω
  have heq : 1 / Real.sqrt (2 * (r : ℝ) / N)
      = Real.sqrt (N / (r : ℝ)) / Real.sqrt 2 := by
    rw [one_div, ← Real.sqrt_inv]
    rw [show (2 * (r : ℝ) / N)⁻¹ = (N / (r : ℝ)) / 2 by field_simp]
    rw [Real.sqrt_div (by positivity) (2 : ℝ)]
  have hinv : 1 / omegaR r m ≤ Real.sqrt (N / (r : ℝ)) / Real.sqrt 2 :=
    le_trans hinv1 heq.le
  have hcoef : 0 ≤ Real.pi / 2 + |φ| := by positivity
  have hstep1 : (Real.pi / 2 - φ) / omegaR r m
      ≤ (Real.pi / 2 + |φ|) / omegaR r m := by
    gcongr
    linarith [neg_le_abs φ]
  have hstep2 : (Real.pi / 2 + |φ|) / omegaR r m
      ≤ (Real.pi / 2 + |φ|) * Real.sqrt (N / (r : ℝ)) / Real.sqrt 2 := by
    rw [div_eq_mul_inv]
    calc (Real.pi / 2 + |φ|) * (omegaR r m)⁻¹
        ≤ (Real.pi / 2 + |φ|) * (Real.sqrt (N / (r : ℝ)) / Real.sqrt 2) := by
          apply mul_le_mul_of_nonneg_left _ hcoef
          rwa [one_div] at hinv
      _ = (Real.pi / 2 + |φ|) * Real.sqrt (N / (r : ℝ)) / Real.sqrt 2 := by ring
  calc (Real.pi / 2 - φ) / omegaR r m
      ≤ (Real.pi / 2 + |φ|) / omegaR r m := hstep1
    _ ≤ (Real.pi / 2 + |φ|) * Real.sqrt (N / (r : ℝ)) / Real.sqrt 2 := hstep2
    _ = (Real.pi / 2 + |φ|) * Real.sqrt (((r + m : ℕ) : ℝ) / (r : ℝ)) / Real.sqrt 2 := by
        rw [hNdef]

end Qatlib.Papers.GroverArbAmp98.MainResults.MeasurementTime
