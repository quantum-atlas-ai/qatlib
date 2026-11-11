/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.NhdsWithin

/-!
# Confluent series and Bessel amplitudes

This module defines the confluent series `zeroFone1` and `zeroFone2`, the order-zero and
order-one Bessel series, and the scaled confluent amplitudes used in the continuum calculation.
The series identities rewrite the confluent functions at negative squares in terms of Bessel
functions. See [Meyer1996a].

## Main statements

* `besselJ0_zeroFone`: The identity `J₀(2z) = ₀F₁(; 1; -z²)` for the defined complex series.
* `besselJ1_zeroFone`: The identity `J₁(2z) = z * ₀F₁(; 2; -z²)` for the defined complex series.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The confluent hypergeometric series ₀F₁ with parameter one, given by the sum of `z^n /
(n!)²`. -/
def zeroFone1 (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((Nat.factorial n : ℂ) * (Nat.factorial n : ℂ))

/-- The confluent hypergeometric series ₀F₁ with parameter two, given by the sum of `z^n / ((n +
1)! * n!)`. -/
def zeroFone2 (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((Nat.factorial (n + 1) : ℂ) * (Nat.factorial n : ℂ))

/-- The order-zero Bessel function defined by its complex power series. -/
def besselJ0 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (z / 2) ^ (2 * n) / ((Nat.factorial n : ℂ) ^ 2)

/-- The order-one Bessel function defined by its complex power series. -/
def besselJ1 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (z / 2) ^ (2 * n + 1) /
    ((Nat.factorial n : ℂ) * (Nat.factorial (n + 1) : ℂ))

/-- The real quantity `2 * √(u * v)` used in the continuum Bessel argument. -/
def tau (u v : ℝ) : ℝ := 2 * Real.sqrt (u * v)

/-- The odd confluent amplitude with prefactor `i * tan (ε * θ)` and ₀F₁ parameter one at
argument `-(u * v / ε²) * tan² (ε * θ)`. -/
def confluentOddAmp (θ u v ε : ℝ) : ℂ :=
  (I * Complex.ofReal (Real.tan (ε * θ))) *
    zeroFone1 (Complex.ofReal (-((u * v) / ε ^ 2 * (Real.tan (ε * θ)) ^ 2)))

/-- The even confluent amplitude with prefactor `-(u / ε) * tan² (ε * θ)` and ₀F₁ parameter two
at argument `-(u * v / ε²) * tan² (ε * θ)`. -/
def confluentEvenAmp (θ u v ε : ℝ) : ℂ :=
  Complex.ofReal (-((u / ε) * (Real.tan (ε * θ)) ^ 2)) *
    zeroFone2 (Complex.ofReal (-((u * v) / ε ^ 2 * (Real.tan (ε * θ)) ^ 2)))

/-- The identity `J₀(2z) = ₀F₁(; 1; -z²)` for the defined complex series. See [Meyer1996a]. -/
theorem besselJ0_zeroFone (z : ℂ) : besselJ0 (2 * z) = zeroFone1 (-(z ^ 2)) := by
  unfold besselJ0 zeroFone1
  apply tsum_congr
  intro n
  have hp : (-(z ^ 2)) ^ n = (-1 : ℂ) ^ n * (z ^ 2) ^ n := by
    rw [neg_eq_neg_one_mul, mul_pow]
  simp only [show (2 * z) / 2 = z by ring, hp, pow_mul]
  ring

/-- The identity `J₁(2z) = z * ₀F₁(; 2; -z²)` for the defined complex series. See [Meyer1996a]. -/
theorem besselJ1_zeroFone (z : ℂ) : besselJ1 (2 * z) = z * zeroFone2 (-(z ^ 2)) := by
  unfold besselJ1 zeroFone2
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [show (2 * z) / 2 = z by ring, pow_succ, pow_mul]
  ring

end Qatlib.Papers.QCellAutomata96.MainResults
