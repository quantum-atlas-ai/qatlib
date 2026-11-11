/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Fourier and stationary-phase expressions for line walks

This module defines the Hadamard Fourier kernel, its dispersion relation, the parity-filtered
integral amplitudes `psiL` and `psiR`, and their probability mass. It also introduces
stationary-phase expressions, the proposed asymptotic formula, and a coin-angle family of
dispersion and curvature functions used in [NayakVishwanath2000].

## Main statements

* `hadamardKernel`: defines the two-dimensional Fourier-space step matrix.
* `probMass`: sums the left and right squared amplitude norms.
* `asymProb`: defines the oscillatory stationary-phase probability expression.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real MeasureTheory
open scoped Interval

noncomputable section

/-- The positive real square root of two. -/
def sqrtTwo : ℝ := Real.sqrt 2

/-- The Hadamard dispersion relation `arcsin (sin k / √2)`. -/
def dispersion (k : ℝ) : ℝ := Real.arcsin (Real.sin k / Real.sqrt 2)

/-- The two-by-two Hadamard Fourier kernel with phases `exp (-i * k)` in the first row and `exp
(i * k)` in the second row. -/
def hadamardKernel (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) •
    !![Complex.exp (-(Complex.I * (k : ℂ))), Complex.exp (-(Complex.I * (k : ℂ)));
       Complex.exp (Complex.I * (k : ℂ)), -Complex.exp (Complex.I * (k : ℂ))]

/-- The parity factor equal to two when `n + t` is even and zero otherwise. -/
def parityWeight (n : ℤ) (t : ℕ) : ℝ := if Even (n + (t : ℤ)) then 2 else 0

/-- The left amplitude defined by the parity-filtered Fourier integral with weight `1 + cos k /
√(1 + cos² k)`. -/
def psiL (n : ℤ) (t : ℕ) : ℂ :=
  (parityWeight n t / 2 : ℂ) *
    ∫ k in (-Real.pi)..Real.pi,
      ((1 + Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((dispersion k : ℂ) * (t : ℂ) + (k : ℂ) * (n : ℂ)))) /
        (2 * (Real.pi : ℂ))

/-- The right amplitude defined by the parity-filtered Fourier integral with weight `exp (i * k)
/ √(1 + cos² k)`. -/
def psiR (n : ℤ) (t : ℕ) : ℂ :=
  (parityWeight n t / 2 : ℂ) *
    ∫ k in (-Real.pi)..Real.pi,
      (Complex.exp (Complex.I * (k : ℂ)) /
          (Real.sqrt (1 + Real.cos k ^ 2) : ℂ)) *
        Complex.exp (-(Complex.I * ((dispersion k : ℂ) * (t : ℂ) + (k : ℂ) * (n : ℂ)))) /
        (2 * (Real.pi : ℂ))

/-- The probability mass obtained by adding the squared complex norms of the left and right
amplitudes. -/
def probMass (n : ℤ) (t : ℕ) : ℝ := Complex.normSq (psiL n t) + Complex.normSq (psiR n t)

/-- The stationary-point expression `arccos (-α / √(1 - α²))`. -/
def kAlpha (α : ℝ) : ℝ := Real.arccos (-α / Real.sqrt (1 - α ^ 2))

/-- The phase `-(dispersion (kAlpha α) + α * kAlpha α)` evaluated at the stationary-point
expression. -/
def phaseFn (α : ℝ) : ℝ := -(dispersion (kAlpha α) + α * kAlpha α)

/-- The phase function `-(dispersion k + α * k)`. -/
def phaseK (k α : ℝ) : ℝ := -(dispersion k + α * k)

/-- The stationary curvature expression `(1 - α²) * √(1 - 2 * α²)`. -/
def omegaSecondAtStationary (α : ℝ) : ℝ := (1 - α ^ 2) * Real.sqrt (1 - 2 * α ^ 2)

/-- The parity-weighted oscillatory probability expression at scaled position `α = n / t`, with
denominator `π * t * |omegaSecondAtStationary α|`. -/
def asymProb (n : ℤ) (t : ℕ) : ℝ :=
  let α : ℝ := (n : ℝ) / (t : ℝ)
  parityWeight n t /
      (Real.pi * (t : ℝ) * |omegaSecondAtStationary α|) *
    ((1 - α) ^ 2 * Real.cos (phaseFn α * (t : ℝ) + Real.pi / 4) ^ 2 +
      (1 - α ^ 2) * Real.cos (phaseFn α * (t : ℝ) + kAlpha α + Real.pi / 4) ^ 2)

/-- The coin-angle dispersion relation `arccos (cos (θ / 2) * cos k)`. -/
def dispersionTheta (θ k : ℝ) : ℝ := Real.arccos (Real.cos (θ / 2) * Real.cos k)

/-- The parameterized stationary-point expression `arcsin (α / √(1 - α²) * tan (θ / 2))`. -/
def kAlphaTheta (θ α : ℝ) : ℝ :=
  Real.arcsin (α / Real.sqrt (1 - α ^ 2) * Real.tan (θ / 2))

/-- The parameterized stationary curvature expression `(1 - α²) * √(cos² (θ / 2) - α²) / sin (θ
/ 2)`. -/
def omegaSecondAtStationaryTheta (θ α : ℝ) : ℝ :=
  (1 - α ^ 2) * Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) / Real.sin (θ / 2)

/-- The slow probability expression `(1 - α) / (π * t * |omegaSecondAtStationary α|)`. -/
def pSlow (α : ℝ) (t : ℕ) : ℝ :=
  (1 - α) / (Real.pi * (t : ℝ) * |omegaSecondAtStationary α|)

/-- The time-independent expression `(1 - α) / (π * |omegaSecondAtStationary α|)`. -/
def momentDensity (α : ℝ) : ℝ := (1 - α) / (Real.pi * |omegaSecondAtStationary α|)

/-- Half the infinite sum of absolute differences between two real mass functions on the
integers. -/
def tvDistance (p u : ℤ → ℝ) : ℝ := (1 / 2) * ∑' n : ℤ, |p n - u n|

end

end Qatlib.Papers.QWalkLine00.MainResults
