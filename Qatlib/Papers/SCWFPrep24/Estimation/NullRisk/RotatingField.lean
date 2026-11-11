/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.RotatingSpinor
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.GridParity

set_option backward.isDefEq.respectTransparency false

/-!
# Rotating Field

The actual nonconstant periodic Fourier mode in one selected physical coordinate, using the canonical additive character.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The actual nonconstant periodic Fourier mode in one selected physical coordinate, using the canonical additive character. -/
def gridFirstMode (d N : ℕ) [NeZero N] (j : Fin d) (x : Fin d → Fin N) : ℂ :=
  ZMod.stdAddChar ((ZMod.finEquiv N) (x j))

/-- Every value of the actual periodic first mode has exactly unit norm square. -/
theorem gridFirstMode_normSq (d N : ℕ) [NeZero N] (j : Fin d) (x : Fin d → Fin N) :
    Complex.normSq (gridFirstMode d N j x) = 1 := by
  simp only [gridFirstMode, ZMod.stdAddChar_apply, Circle.normSq_coe]

/-- An actual canonical periodic unit shift multiplies its selected Fourier mode by the canonical character of one. -/
theorem gridFirstMode_unit_shift (d N : ℕ) [NeZero N] (j : Fin d)
    (x : Fin d → Fin N) :
    gridFirstMode d N j (periodicUnitShift d N j x) =
      ZMod.stdAddChar (1 : ZMod N)*gridFirstMode d N j x := by
  simp only [gridFirstMode, periodic_unit_shift_coordinates, ite_true,
    AddChar.map_add_eq_mul]
  ring

/-- The canonical character of one has the exact physical mesh-angle sine as its imaginary part. -/
theorem stdAddChar_one_im (N : ℕ) [NeZero N] :
    (ZMod.stdAddChar (1 : ZMod N)).im = Real.sin (2*Real.pi/N) := by
  have h := ZMod.stdAddChar_coe (N := N) 1
  norm_num only [Int.cast_one, mul_one] at h
  have he : 2*(Real.pi : ℂ)*Complex.I/(N : ℂ) =
      ((2*Real.pi/N : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [h, he, Complex.exp_ofReal_mul_I_im]

/-- The complete periodic Fourier mode sums to zero by actual bijective translation and nontriviality; no address-first reduction is used. -/
theorem gridFirstMode_sum_zero (d N : ℕ) [NeZero N] [Fact (1 < N)] (j : Fin d) :
    (∑ x, gridFirstMode d N j x) = 0 := by
  have hq : ZMod.stdAddChar (1 : ZMod N) ≠ 1 := by
    intro h
    have h0 : ZMod.stdAddChar (1 : ZMod N) = ZMod.stdAddChar (0 : ZMod N) := by
      simpa only [AddChar.map_zero_eq_one] using h
    exact one_ne_zero (ZMod.injective_stdAddChar h0)
  have hs := Equiv.sum_comp (periodicUnitShift d N j) (gridFirstMode d N j)
  simp_rw [gridFirstMode_unit_shift, ← Finset.mul_sum] at hs
  have hm : (ZMod.stdAddChar (1 : ZMod N)-1)*(∑ x, gridFirstMode d N j x) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hq)

/-- The actual slow-rotation alternative retains its fixed global frame phase and both original Fourier modes. -/
def rotatingField (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (x : Fin d → Fin N) : Bool → ℂ :=
  rotatingSpinor (α*gridFirstMode d N j x) (star α)

/-- Every member of the actual periodic slow-rotation field is pointwise normalized. -/
theorem rotatingField_mass (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (hα : Complex.normSq α = 1) (x : Fin d → Fin N) :
    qubitMass (rotatingField d N j α x) = 1 := by
  simp only [rotatingField, rotatingSpinor_mass, Complex.normSq_mul,
    gridFirstMode_normSq, Complex.star_def, Complex.normSq_conj, hα]
  norm_num

/-- The actual first source Bloch coordinate of the slow-rotation field is the imaginary part of its nonconstant mode. -/
theorem rotatingField_bloch_zero (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (x : Fin d → Fin N) :
    qubitBloch (rotatingField d N j α x) 0 = (α^2*gridFirstMode d N j x).im := by
  rw [rotatingField, rotatingSpinor_bloch_zero]
  simp only [star_star]
  congr 1
  ring

/-- The actual second source Bloch coordinate vanishes on the normalized slow-rotation field. -/
theorem rotatingField_bloch_one (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (hα : Complex.normSq α = 1) (x : Fin d → Fin N) :
    qubitBloch (rotatingField d N j α x) 1 = 0 := by
  simp only [rotatingField, rotatingSpinor_bloch_one, Complex.normSq_mul,
    gridFirstMode_normSq, Complex.star_def, Complex.normSq_conj, hα]
  norm_num

/-- The actual third source Bloch coordinate of the slow-rotation field is the real part of its nonconstant mode. -/
theorem rotatingField_bloch_two (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (x : Fin d → Fin N) :
    qubitBloch (rotatingField d N j α x) 2 = (α^2*gridFirstMode d N j x).re := by
  rw [rotatingField, rotatingSpinor_bloch_two]
  simp only [star_star]
  congr 1
  ring

/-- The actual periodic slow-rotation field has exactly zero global source Bloch vector for every unit global frame phase. -/
theorem rotatingField_global_bloch_zero (d N : ℕ) [NeZero N] [Fact (1 < N)]
    (j : Fin d) (α : ℂ) (hα : Complex.normSq α = 1) (i : Fin 3) :
    (∑ x, qubitBloch (rotatingField d N j α x) i) = 0 := by
  fin_cases i
  · change (∑ x, qubitBloch (rotatingField d N j α x) 0) = 0
    simp_rw [rotatingField_bloch_zero, ← Complex.im_sum]
    rw [← Finset.mul_sum, gridFirstMode_sum_zero, mul_zero, Complex.zero_im]
  · change (∑ x, qubitBloch (rotatingField d N j α x) 1) = 0
    simp_rw [rotatingField_bloch_one d N j α hα, Finset.sum_const_zero]
  · change (∑ x, qubitBloch (rotatingField d N j α x) 2) = 0
    simp_rw [rotatingField_bloch_two, ← Complex.re_sum]
    rw [← Finset.mul_sum, gridFirstMode_sum_zero, mul_zero, Complex.zero_re]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
