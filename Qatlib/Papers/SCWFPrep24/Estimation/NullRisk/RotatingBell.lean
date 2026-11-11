/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.RotatingField

set_option backward.isDefEq.respectTransparency false

/-!
# Rotating Bell

The actual double periodic shift acts by the square of the standard character in the selected coordinate, and by the identity in every other coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The actual double periodic shift acts by the square of the standard character in the selected coordinate, and by the identity in every other coordinate. -/
theorem gridFirstMode_double_shift (d N : ℕ) [NeZero N] (j k : Fin d)
    (x : Fin d → Fin N) :
    gridFirstMode d N j (periodicDoubleShift d N k x) =
      (if k=j then (ZMod.stdAddChar (1 : ZMod N))^2 else 1)*gridFirstMode d N j x := by
  have htwo : ZMod.stdAddChar (2 : ZMod N) = (ZMod.stdAddChar (1 : ZMod N))^2 := by
    rw [show (2 : ZMod N) = 1+1 by ring, AddChar.map_add_eq_mul, pow_two]
  by_cases hk : k=j
  · subst k
    simp only [gridFirstMode, periodic_double_shift_coordinates, ite_true,
      AddChar.map_add_eq_mul, htwo]
    ring
  · simp only [gridFirstMode, periodic_double_shift_coordinates, ite_eq_right hk,
      ite_eq_right (Ne.symm hk), add_zero, one_mul]

/-- The exact two-mode alternative determinant depends only on the difference of its actual physical Fourier mode values. -/
theorem rotatingField_determinant (d N : ℕ) [NeZero N] (j : Fin d)
    (α : ℂ) (hα : Complex.normSq α = 1) (x y : Fin d → Fin N) :
    determinant (rotatingField d N j α x) (rotatingField d N j α y) =
      Complex.I*(gridFirstMode d N j x-gridFirstMode d N j y)/2 := by
  have ha : α*star α = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hα, Complex.ofReal_one]
  rw [rotatingField, rotatingField, rotatingSpinor_determinant]
  calc Complex.I*((α*gridFirstMode d N j x)*star α-star α*(α*gridFirstMode d N j y))/2 =
       Complex.I*((α*star α)*(gridFirstMode d N j x-gridFirstMode d N j y))/2 := by ring
     _ = _ := by rw [ha, one_mul]

/-- The double-angle chord norm of every unit complex phase is exactly four times its imaginary part squared. -/
theorem unit_phase_double_chord (q : ℂ) (hq : Complex.normSq q = 1) :
    Complex.normSq (1-q^2) = 4*q.im^2 := by
  rw [Complex.normSq_sub, map_one, map_pow, hq]
  simp only [one_mul, Complex.conj_re, pow_two, Complex.mul_re]
  have hn := hq
  rw [Complex.normSq_apply] at hn
  nlinarith

/-- The actual periodic slow-rotation input has the claimed exact singlet probability at every physical double shift, including wrap edges and unused directions. -/
theorem rotatingField_double_bell_probability (d N : ℕ) [NeZero N] (j k : Fin d)
    (α : ℂ) (hα : Complex.normSq α = 1) (x : Fin d → Fin N) :
    bellProbability (rotatingField d N j α x)
      (rotatingField d N j α (periodicDoubleShift d N k x)) =
      if k=j then (Real.sin (2*Real.pi/N))^2/2 else 0 := by
  have hq : Complex.normSq (ZMod.stdAddChar (1 : ZMod N)) = 1 := by
    rw [ZMod.stdAddChar_apply, Circle.normSq_coe]
  rw [bellProbability, rotatingField_determinant d N j α hα,
    gridFirstMode_double_shift]
  by_cases hk : k=j
  · rw [ite_eq_left hk, ite_eq_left hk]
    have he : gridFirstMode d N j x-(ZMod.stdAddChar (1 : ZMod N))^2*gridFirstMode d N j x =
        (1-(ZMod.stdAddChar (1 : ZMod N))^2)*gridFirstMode d N j x := by ring
    rw [he, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_I, gridFirstMode_normSq, unit_phase_double_chord _ hq,
      stdAddChar_one_im]
    norm_num
  · simp only [ite_eq_right hk, one_mul, sub_self, mul_zero, zero_div, map_zero]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
