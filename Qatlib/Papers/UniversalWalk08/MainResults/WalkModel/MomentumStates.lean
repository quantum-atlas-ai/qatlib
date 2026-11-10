/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
set_option warningAsError false

namespace Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore

open Complex

set_option autoImplicit false

def lineOperator (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => f (x + 1) + f (x - 1)

noncomputable def planeWave (k : ℝ) : ℤ → ℂ :=
  fun x => Complex.exp (((k * (x : ℝ) : ℝ) : ℂ) * Complex.I)

theorem exp_ofReal_add_mul_I (a b : ℝ) :
    Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_I_add_exp_neg_I (k : ℝ) :
    Complex.exp ((k : ℂ) * Complex.I) + Complex.exp (((-k : ℝ) : ℂ) * Complex.I) =
      2 * (Real.cos k : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

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

noncomputable def walkEigenvalue (k : ℝ) : ℝ := 2 * Real.cos k

theorem planeWave_norm (k : ℝ) (x : ℤ) : ‖planeWave k x‖ = 1 := by
  unfold planeWave
  rw [Complex.norm_exp_ofReal_mul_I]

theorem planeWave_normSq (k : ℝ) (x : ℤ) :
    Complex.normSq (planeWave k x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, planeWave_norm]
  norm_num

noncomputable def modePhase (k t : ℝ) : ℂ :=
  Complex.exp (((-2 * t * Real.cos k : ℝ) : ℂ) * Complex.I)

theorem modePhase_norm (k t : ℝ) : ‖modePhase k t‖ = 1 := by
  unfold modePhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem modePhase_normSq (k t : ℝ) : Complex.normSq (modePhase k t) = 1 := by
  rw [Complex.normSq_eq_norm_sq, modePhase_norm]
  norm_num

theorem lineOperator_smul (c : ℂ) (f : ℤ → ℂ) :
    lineOperator (c • f) = c • lineOperator f := by
  funext x
  simp only [lineOperator, Pi.smul_apply, smul_eq_mul]
  ring

theorem lineOperator_modeEigen (k t : ℝ) :
    lineOperator (modePhase k t • planeWave k) =
      (2 * Real.cos k) • (modePhase k t • planeWave k) := by
  rw [lineOperator_smul, lineOperator_planeWave]
  exact smul_comm _ _ _

theorem hasDerivAt_walkEigenvalue (k : ℝ) :
    HasDerivAt (fun k => 2 * Real.cos k) (-2 * Real.sin k) k := by
  have h : HasDerivAt (fun k : ℝ => Real.cos k) (-Real.sin k) k := Real.hasDerivAt_cos k
  simpa using h.const_mul 2

noncomputable def groupVelocity (k : ℝ) : ℝ := -2 * Real.sin k

theorem hasDerivAt_eigenvalue_groupVelocity (k : ℝ) :
    HasDerivAt (fun k => walkEigenvalue k) (groupVelocity k) k := by
  simpa [groupVelocity, walkEigenvalue] using hasDerivAt_walkEigenvalue k

theorem groupVelocity_working_momentum :
    groupVelocity (-(Real.pi / 4)) = Real.sqrt 2 := by
  unfold groupVelocity
  rw [Real.sin_neg, Real.sin_pi_div_four]
  ring

noncomputable def stationaryTime (k L : ℝ) : ℝ := L / groupVelocity k

theorem stationaryTime_working_momentum (L : ℝ) :
    stationaryTime (-(Real.pi / 4)) L = L / Real.sqrt 2 := by
  unfold stationaryTime
  rw [groupVelocity_working_momentum]

theorem hasDerivAt_two_mul_sin (t k : ℝ) :
    HasDerivAt (fun k => 2 * t * Real.sin k) (2 * t * Real.cos k) k := by
  have h : HasDerivAt (fun k : ℝ => Real.sin k) (Real.cos k) k := Real.hasDerivAt_sin k
  simpa [mul_assoc, mul_comm, mul_left_comm] using h.const_mul (2 * t)

theorem curvature_working_momentum (t : ℝ) :
    2 * t * Real.cos (-(Real.pi / 4)) = Real.sqrt 2 * t := by
  rw [Real.cos_neg, Real.cos_pi_div_four]
  ring

end Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
