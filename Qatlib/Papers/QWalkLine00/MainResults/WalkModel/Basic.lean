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

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real MeasureTheory
open scoped Interval

noncomputable section

def sqrtTwo : ℝ := Real.sqrt 2

def dispersion (k : ℝ) : ℝ := Real.arcsin (Real.sin k / Real.sqrt 2)

def hadamardKernel (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) •
    !![Complex.exp (-(Complex.I * (k : ℂ))), Complex.exp (-(Complex.I * (k : ℂ)));
       Complex.exp (Complex.I * (k : ℂ)), -Complex.exp (Complex.I * (k : ℂ))]

def parityWeight (n : ℤ) (t : ℕ) : ℝ := if Even (n + (t : ℤ)) then 2 else 0

def psiL (n : ℤ) (t : ℕ) : ℂ :=
  (parityWeight n t / 2 : ℂ) *
    ∫ k in (-Real.pi)..Real.pi,
      ((1 + Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((dispersion k : ℂ) * (t : ℂ) + (k : ℂ) * (n : ℂ)))) /
        (2 * (Real.pi : ℂ))

def psiR (n : ℤ) (t : ℕ) : ℂ :=
  (parityWeight n t / 2 : ℂ) *
    ∫ k in (-Real.pi)..Real.pi,
      (Complex.exp (Complex.I * (k : ℂ)) /
          (Real.sqrt (1 + Real.cos k ^ 2) : ℂ)) *
        Complex.exp (-(Complex.I * ((dispersion k : ℂ) * (t : ℂ) + (k : ℂ) * (n : ℂ)))) /
        (2 * (Real.pi : ℂ))

def probMass (n : ℤ) (t : ℕ) : ℝ := Complex.normSq (psiL n t) + Complex.normSq (psiR n t)

def kAlpha (α : ℝ) : ℝ := Real.arccos (-α / Real.sqrt (1 - α ^ 2))

def phaseFn (α : ℝ) : ℝ := -(dispersion (kAlpha α) + α * kAlpha α)

def phaseK (k α : ℝ) : ℝ := -(dispersion k + α * k)

def omegaSecondAtStationary (α : ℝ) : ℝ := (1 - α ^ 2) * Real.sqrt (1 - 2 * α ^ 2)

def asymProb (n : ℤ) (t : ℕ) : ℝ :=
  let α : ℝ := (n : ℝ) / (t : ℝ)
  parityWeight n t /
      (Real.pi * (t : ℝ) * |omegaSecondAtStationary α|) *
    ((1 - α) ^ 2 * Real.cos (phaseFn α * (t : ℝ) + Real.pi / 4) ^ 2 +
      (1 - α ^ 2) * Real.cos (phaseFn α * (t : ℝ) + kAlpha α + Real.pi / 4) ^ 2)

def dispersionTheta (θ k : ℝ) : ℝ := Real.arccos (Real.cos (θ / 2) * Real.cos k)

def kAlphaTheta (θ α : ℝ) : ℝ :=
  Real.arcsin (α / Real.sqrt (1 - α ^ 2) * Real.tan (θ / 2))

def omegaSecondAtStationaryTheta (θ α : ℝ) : ℝ :=
  (1 - α ^ 2) * Real.sqrt (Real.cos (θ / 2) ^ 2 - α ^ 2) / Real.sin (θ / 2)

def pSlow (α : ℝ) (t : ℕ) : ℝ :=
  (1 - α) / (Real.pi * (t : ℝ) * |omegaSecondAtStationary α|)

def momentDensity (α : ℝ) : ℝ := (1 - α) / (Real.pi * |omegaSecondAtStationary α|)

def tvDistance (p u : ℤ → ℝ) : ℝ := (1 / 2) * ∑' n : ℤ, |p n - u n|

end

end Qatlib.Papers.QWalkLine00.MainResults
