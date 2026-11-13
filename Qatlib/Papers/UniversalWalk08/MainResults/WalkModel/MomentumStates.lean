/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Plane waves and group velocity on the integer line

This module studies the nearest-neighbor line operator and its plane waves, with dispersion
relation `walkEigenvalue k = 2 * cos k`. The functions `modePhase`, `groupVelocity`, and
`stationaryTime` provide the momentum and propagation calculations used in [Childs2009],
including the working velocity `√2` at `-π / 4`.

## Main statements

* `lineOperator_planeWave`: Plane waves are eigenfunctions of the line operator.
* `hasDerivAt_eigenvalue_groupVelocity`: Group velocity is the derivative of the dispersion
  relation.
* `stationaryTime_working_momentum`: The working-momentum stationary time is `L / √2`.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore

open Complex

set_option autoImplicit false

/-- The nearest-neighbor adjacency operator on functions from the integers to the complex
numbers. -/
def lineOperator (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => f (x + 1) + f (x - 1)

/-- The plane wave with value `exp(ikx)` at integer position `x`. -/
noncomputable def planeWave (k : ℝ) : ℤ → ℂ :=
  fun x => Complex.exp (((k * (x : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The complex exponential of `i * (a + b)` factors into the product of the exponentials of
`ia` and `ib`. -/
theorem exp_ofReal_add_mul_I (a b : ℝ) :
    Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The sum `exp(ik) + exp(-ik)` equals complex `2 * cos k`. -/
theorem exp_I_add_exp_neg_I (k : ℝ) :
    Complex.exp ((k : ℂ) * Complex.I) + Complex.exp (((-k : ℝ) : ℂ) * Complex.I) =
      2 * (Real.cos k : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The plane wave of momentum `k` is an eigenfunction of the line operator with eigenvalue `2 *
cos k` [Childs2009]. -/
theorem lineOperator_planeWave (k : ℝ) :
    lineOperator (planeWave k) = (2 * Real.cos k) • planeWave k := by
  funext x
  simp only [lineOperator, planeWave, Pi.smul_apply]
  have h1 : (k * ((x + 1 : ℤ) : ℝ) : ℝ) = k * (x : ℝ) + k := by push_cast; ring
  have h2 : (k * ((x - 1 : ℤ) : ℝ) : ℝ) = k * (x : ℝ) + (-k) := by push_cast; ring
  rw [h1, h2, exp_ofReal_add_mul_I, exp_ofReal_add_mul_I]
  rw [← mul_add, exp_I_add_exp_neg_I, Complex.real_smul]
  push_cast
  ring

/-- The real dispersion value `2 * cos k`. -/
noncomputable def walkEigenvalue (k : ℝ) : ℝ := 2 * Real.cos k

/-- Every value of a plane wave has norm one. -/
theorem planeWave_norm (k : ℝ) (x : ℤ) : ‖planeWave k x‖ = 1 := by
  unfold planeWave
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Every value of a plane wave has squared modulus one. -/
theorem planeWave_normSq (k : ℝ) (x : ℤ) :
    Complex.normSq (planeWave k x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, planeWave_norm]
  norm_num

/-- The time-evolution phase `exp(-2it cos k)` of a momentum mode. -/
noncomputable def modePhase (k t : ℝ) : ℂ :=
  Complex.exp (((-2 * t * Real.cos k : ℝ) : ℂ) * Complex.I)

/-- The time-evolution phase of a momentum mode has norm one. -/
theorem modePhase_norm (k t : ℝ) : ‖modePhase k t‖ = 1 := by
  unfold modePhase
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The time-evolution phase of a momentum mode has squared modulus one. -/
theorem modePhase_normSq (k t : ℝ) : Complex.normSq (modePhase k t) = 1 := by
  rw [Complex.normSq_eq_norm_sq, modePhase_norm]
  norm_num

/-- The line operator commutes with multiplication by a complex scalar. -/
theorem lineOperator_smul (c : ℂ) (f : ℤ → ℂ) :
    lineOperator (c • f) = c • lineOperator f := by
  funext x
  simp only [lineOperator, Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplying a plane wave by its time-evolution phase preserves its line-operator eigenvalue
`2 * cos k` [Childs2009]. -/
theorem lineOperator_modeEigen (k t : ℝ) :
    lineOperator (modePhase k t • planeWave k) =
      (2 * Real.cos k) • (modePhase k t • planeWave k) := by
  rw [lineOperator_smul, lineOperator_planeWave]
  exact smul_comm _ _ _

/-- The derivative of `2 * cos k` at `k` is `-2 * sin k`. -/
theorem hasDerivAt_walkEigenvalue (k : ℝ) :
    HasDerivAt (fun k => 2 * Real.cos k) (-2 * Real.sin k) k := by
  have h : HasDerivAt (fun k : ℝ => Real.cos k) (-Real.sin k) k := Real.hasDerivAt_cos k
  simpa using h.const_mul 2

/-- The group velocity `-2 * sin k`. -/
noncomputable def groupVelocity (k : ℝ) : ℝ := -2 * Real.sin k

/-- The derivative of the dispersion relation at `k` equals `groupVelocity k`. -/
theorem hasDerivAt_eigenvalue_groupVelocity (k : ℝ) :
    HasDerivAt (fun k => walkEigenvalue k) (groupVelocity k) k := by
  simpa [groupVelocity, walkEigenvalue] using hasDerivAt_walkEigenvalue k

/-- The group velocity at momentum `-π / 4` is `√2` [Childs2009]. -/
theorem groupVelocity_working_momentum :
    groupVelocity (-(Real.pi / 4)) = Real.sqrt 2 := by
  unfold groupVelocity
  rw [Real.sin_neg, Real.sin_pi_div_four]
  ring

/-- The stationary propagation time `L / groupVelocity k`. -/
noncomputable def stationaryTime (k L : ℝ) : ℝ := L / groupVelocity k

/-- At momentum `-π / 4`, the stationary time for length `L` is `L / √2` [Childs2009]. -/
theorem stationaryTime_working_momentum (L : ℝ) :
    stationaryTime (-(Real.pi / 4)) L = L / Real.sqrt 2 := by
  unfold stationaryTime
  rw [groupVelocity_working_momentum]

/-- The derivative of `2 * t * sin k` with respect to `k` is `2 * t * cos k`. -/
theorem hasDerivAt_two_mul_sin (t k : ℝ) :
    HasDerivAt (fun k => 2 * t * Real.sin k) (2 * t * Real.cos k) k := by
  have h : HasDerivAt (fun k : ℝ => Real.sin k) (Real.cos k) k := Real.hasDerivAt_sin k
  simpa [mul_assoc, mul_comm, mul_left_comm] using h.const_mul (2 * t)

/-- At momentum `-π / 4`, the curvature expression `2 * t * cos k` equals `√2 * t` [Childs2009]. -/
theorem curvature_working_momentum (t : ℝ) :
    2 * t * Real.cos (-(Real.pi / 4)) = Real.sqrt 2 * t := by
  rw [Real.cos_neg, Real.cos_pi_div_four]
  ring

end Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
