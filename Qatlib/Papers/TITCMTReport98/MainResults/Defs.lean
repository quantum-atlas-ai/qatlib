/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Displayed formulas for annealing schedules

This module collects the scalar expressions used to study annealing schedules in
[KadowakiNishimori1998]. It defines squared amplitude readout through `groundProb`, displayed
Landau-Zener and inverse-schedule expressions, and gamma-function coefficients for the
square-root schedule.

The definitions keep the displayed weights and their complements explicit. `nearZeroPhase`
records the logarithmic complex phase used near zero.

## Main statements

* `groundProb_eq_one_sub`: expresses one squared amplitude using normalization.
* `inverseScheduleCoeff`: the gamma-function coefficient for the inverse schedule.
* `sqrtScheduleModeCoeff1` and `sqrtScheduleModeCoeff2`: the two square-root-schedule mode
  coefficients.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Complex

/-- The squared complex norm of the amplitude `a t`. -/
def groundProb (a : ℝ → ℂ) (t : ℝ) : ℝ := ‖a t‖ ^ 2

/-- If the squared norms of `a t` and `b t` sum to one, then `groundProb a t` equals `1 - ‖b t‖
^ 2`. -/
theorem groundProb_eq_one_sub (a b : ℝ → ℂ) (t : ℝ)
    (h : ‖a t‖ ^ 2 + ‖b t‖ ^ 2 = 1) : groundProb a t = 1 - ‖b t‖ ^ 2 := by
  unfold groundProb
  linarith

/-- The displayed complex Landau-Zener amplitude expression in terms of powers, exponentials,
and gamma functions. -/
def landauZenerDisplayedAmplitude (h c : ℝ) : ℂ :=
  -((h : ℂ) * (Real.sqrt Real.pi : ℂ)
        * (2 : ℂ) ^ (-(I * (h : ℂ) ^ 2 / (4 * (c : ℂ))))
        * Complex.exp (-(Real.pi * (h : ℂ) ^ 2 / (8 * (c : ℂ)))))
      / (2 * Real.sqrt (2 * c))
    * ((Complex.Gamma (1 + I * (h : ℂ) ^ 2 / (4 * (c : ℂ))))⁻¹
        + (Real.sqrt c : ℂ) * Complex.exp (3 * (Real.pi : ℂ) * I / 4)
            * (1 + I * (h : ℂ) ^ 2 / (2 * (c : ℂ)))
            / ((h : ℂ) * Complex.Gamma (3 / 2 + I * (h : ℂ) ^ 2 / (4 * (c : ℂ)))))

/-- One minus the squared norm of `landauZenerDisplayedAmplitude h c`. -/
def landauZenerDisplayedComplement (h c : ℝ) : ℝ := 1 - ‖landauZenerDisplayedAmplitude h c‖ ^ 2

/-- The coefficient `√2 * (2h) ^ (-ic) * Γ(2ic) / Γ(ic)` for the inverse-schedule expression. -/
def inverseScheduleCoeff (h c : ℝ) : ℂ :=
  (Real.sqrt 2 : ℂ) * ((2 : ℂ) * (h : ℂ)) ^ (-(I * (c : ℂ)))
    * Complex.Gamma (I * 2 * (c : ℂ)) / Complex.Gamma (I * (c : ℂ))

/-- The displayed inverse-schedule weight, consisting of a hyperbolic-sine prefactor times
constant, oscillatory inverse-time, and inverse-square-time terms. -/
def inverseScheduleDisplayedWeight (h c : ℝ) (t : ℝ) : ℝ :=
  Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c)
    * (Real.exp (-(Real.pi * c)) + c * Real.cos (2 * h * t) / (h * t)
        + c ^ 2 * Real.exp (Real.pi * c) / (4 * h ^ 2 * t ^ 2))

/-- One minus the displayed inverse-schedule weight. -/
def inverseScheduleDisplayedComplement (h c : ℝ) (t : ℝ) : ℝ :=
  1 - inverseScheduleDisplayedWeight h c t

/-- The displayed square-root-schedule weight as `π * exp (-γπ) / 2` times the squared norm of a
sum of two reciprocal-gamma terms. -/
def sqrtScheduleDisplayedWeight (γ : ℝ) : ℝ :=
  Real.pi * Real.exp (-(γ * Real.pi)) / 2
    * ‖(Complex.Gamma (1 / 2 - I * (γ : ℂ)))⁻¹
        + ((Real.sqrt γ)⁻¹ : ℂ) * Complex.exp (5 * (Real.pi : ℂ) * I / 4)
            * (Complex.Gamma (-(I * (γ : ℂ))))⁻¹‖ ^ 2

/-- One minus the displayed square-root-schedule weight. -/
def sqrtScheduleDisplayedComplement (γ : ℝ) : ℝ := 1 - sqrtScheduleDisplayedWeight γ

/-- The reciprocal gamma coefficient `Γ(1 / 2 - i * c ^ 2 / (2h))⁻¹`. -/
def sqrtScheduleModeCoeff1 (h c : ℝ) : ℂ :=
  (Complex.Gamma (1 / 2 - I * ((c : ℂ) ^ 2 / (2 * (h : ℂ)))))⁻¹

/-- The mode coefficient `ih / c ^ 2` times `Γ(-i * c ^ 2 / (2h))⁻¹`. -/
def sqrtScheduleModeCoeff2 (h c : ℝ) : ℂ :=
  I * (h : ℂ) / ((c : ℂ) ^ 2)
    * (Complex.Gamma (-(I * ((c : ℂ) ^ 2 / (2 * (h : ℂ))))))⁻¹

/-- The logarithmic phase `exp (i * c * log t)`, using the real logarithm. -/
def nearZeroPhase (c t : ℝ) : ℂ :=
  Complex.exp (I * (c : ℂ) * (Real.log t : ℂ))

end Qatlib.Papers.TITCMTReport98.MainResults
