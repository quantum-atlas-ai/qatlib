/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.Checkerboard
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option backward.isDefEq.respectTransparency false

/-!
# Rotating Spinor

The physical two-component rotating spinor in its exact two-Fourier-mode form.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The physical two-component rotating spinor in its exact two-Fourier-mode form. -/
def rotatingSpinor (a b : ℂ) (s : Bool) : ℂ :=
  if s then -Complex.I*(a-b)/2 else (a+b)/2

/-- The exact physical norm of the two-mode spinor is the mean of the two mode norms. -/
theorem rotatingSpinor_mass (a b : ℂ) :
    qubitMass (rotatingSpinor a b) = (Complex.normSq a+Complex.normSq b)/2 := by
  simp only [qubitMass, rotatingSpinor, Bool.false_eq_true, ite_false, ite_true,
    Complex.normSq_div, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I]
  norm_num [Complex.normSq_add, Complex.normSq_sub]
  ring

/-- The literal singlet determinant of two two-mode spinors retains all complex amplitudes. -/
theorem rotatingSpinor_determinant (a b c d : ℂ) :
    determinant (rotatingSpinor a b) (rotatingSpinor c d) =
      Complex.I*(a*d-b*c)/2 := by
  simp only [determinant, rotatingSpinor, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- The first exact source Bloch coordinate of the two-mode spinor. -/
theorem rotatingSpinor_bloch_zero (a b : ℂ) :
    qubitBloch (rotatingSpinor a b) 0 = (a*star b).im := by
  simp [qubitBloch, pauliField, rotatingSpinor,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The second exact source Bloch coordinate records the mode mass imbalance. -/
theorem rotatingSpinor_bloch_one (a b : ℂ) :
    qubitBloch (rotatingSpinor a b) 1 = (Complex.normSq b-Complex.normSq a)/2 := by
  simp [qubitBloch, pauliField, rotatingSpinor,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- The third exact source Bloch coordinate is the real part of the mode cross product. -/
theorem rotatingSpinor_bloch_two (a b : ℂ) :
    qubitBloch (rotatingSpinor a b) 2 = (a*star b).re := by
  simp [qubitBloch, pauliField, rotatingSpinor,
    Complex.mul_re, Complex.mul_im]
  ring

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
