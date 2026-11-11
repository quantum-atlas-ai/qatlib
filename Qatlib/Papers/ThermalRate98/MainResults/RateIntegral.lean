/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.PhysicalRateFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite time integrals of spectral correlations

This module defines `eq16Correlation`, a finite spectral sum of thermal weights, oscillatory
phases, squared energy gaps, and squared overlap norms from the correlation analysis of
[LidarWang1999]. It removes the diagonal terms and evaluates the interval integral term by term
when distinct indices have nonzero energy gaps and `ħ` is nonzero.

The quantity `thermalRateWindow` multiplies this finite time integral by the inverse reactant
factor `Qr`. Its spectral formula uses the explicit integrated phase factor.

## Main statements

* `intervalIntegral_eq16Correlation`: evaluates the finite time integral of the spectral double
  sum.
* `thermalRateWindow_eq_spectral`: expresses the normalized window integral in spectral form.
* `thermalRateWindow_zero`: gives the value at a zero time window.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite spectral double sum of thermal weights, time evolution phases, squared energy
differences, and squared overlap norms. -/
def eq16Correlation (β t ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) : ℂ :=
  ∑ n, ∑ m, Complex.exp (-(β * (E n + E m)) / 2) *
    Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
    (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ)

/-- The spectral correlation sum is unchanged by restricting to distinct indices, since its
diagonal terms vanish. See [LidarWang1999]. -/
theorem eq16Correlation_offdiag (β t ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) :
    eq16Correlation β t ħ E S =
      ∑ n, ∑ m ∈ Finset.univ.erase n,
        Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ) := by
  unfold eq16Correlation
  exact (source_flux_offdiagonal β t ħ E S).symm

/-- For nonzero energy gap and nonzero `ħ`, a thermal oscillatory term integrates over `0..T` to
its constant prefactor times `(exp (i * ω * T) - 1) / (i * ω)`, where `ω = (em - en) / ħ`. -/
theorem integral_eq16_term (β ħ en em : ℝ) (F : ℂ) (T : ℝ)
    (hω : em - en ≠ 0) (hħ : ħ ≠ 0) :
    (∫ t in (0 : ℝ)..T,
        Complex.exp (-(β * (en + em)) / 2) *
          Complex.exp (Complex.I * ((em - en) * t / ħ)) * F) =
      Complex.exp (-(β * (en + em)) / 2) * F *
        ((Complex.exp (Complex.I * (((em - en) / ħ : ℝ) : ℂ) * T) - 1) /
          (Complex.I * (((em - en) / ħ : ℝ) : ℂ))) := by
  have harg : ∀ t : ℝ, Complex.I * ((em - en) * t / ħ) =
      (Complex.I * (((em - en) / ħ : ℝ) : ℂ)) * t := by
    intro t
    push_cast
    ring
  have hEq : (fun t : ℝ => Complex.exp (-(β * (en + em)) / 2) *
        Complex.exp (Complex.I * ((em - en) * t / ħ)) * F) =
      fun t : ℝ => (Complex.exp (-(β * (en + em)) / 2) * F) *
        Complex.exp ((Complex.I * (((em - en) / ħ : ℝ) : ℂ)) * t) := by
    funext t
    rw [harg t]
    ring
  rw [hEq, intervalIntegral.integral_const_mul]
  have ha : Complex.I * (((em - en) / ħ : ℝ) : ℂ) ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    have hdiv : ((em - en) / ħ : ℝ) ≠ 0 := div_ne_zero hω hħ
    exact_mod_cast hdiv
  rw [integral_exp_mul_complex ha]
  simp

/-- When all energy gaps between distinct indices and `ħ` are nonzero, the interval integral of
the spectral correlation equals the sum of its explicitly integrated off-diagonal terms. See
[LidarWang1999]. -/
theorem intervalIntegral_eq16Correlation (β ħ T : ℝ) (E : I → ℝ) (S : I → I → ℂ)
    (hω : ∀ n m, n ≠ m → E m - E n ≠ 0) (hħ : ħ ≠ 0) :
    (∫ t in (0 : ℝ)..T, eq16Correlation β t ħ E S) =
      ∑ n, ∑ m ∈ Finset.univ.erase n,
        Complex.exp (-(β * (E n + E m)) / 2) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ) *
          ((Complex.exp (Complex.I * (((E m - E n) / ħ : ℝ) : ℂ) * T) - 1) /
            (Complex.I * (((E m - E n) / ħ : ℝ) : ℂ))) := by
  have hterm : ∀ (n m : I), m ≠ n →
      Continuous (fun t : ℝ =>
        Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ)) := by
    intro n m _
    fun_prop
  unfold eq16Correlation
  simp only [← source_flux_offdiagonal]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≠ n := Finset.ne_of_mem_erase hm
      have h := integral_eq16_term β ħ (E n) (E m)
        (((E n - E m : ℝ) : ℂ) ^ 2 * (Complex.normSq (S n m) : ℂ)) T
        (hω n m hmn.symm) hħ
      simpa only [mul_assoc] using h
    · intro m hm
      exact (hterm n m (Finset.ne_of_mem_erase hm)).intervalIntegrable 0 T
  · intro n _
    exact (continuous_finsetSum _ (fun m hm => hterm n m
      (Finset.ne_of_mem_erase hm))).intervalIntegrable 0 T

/-- The inverse reactant factor `Qr⁻¹` times the interval integral of `eq16Correlation` over
`0..T`. -/
def thermalRateWindow (Qr : ℂ) (β ħ T : ℝ) (E : I → ℝ) (S : I → I → ℂ) : ℂ :=
  Qr⁻¹ * ∫ t in (0 : ℝ)..T, eq16Correlation β t ħ E S

/-- For nonzero `ħ` and nonzero gaps between distinct energy indices, the normalized finite time
window equals `Qr⁻¹` times the explicit integrated spectral double sum. See [LidarWang1999]. -/
theorem thermalRateWindow_eq_spectral (Qr : ℂ) (β ħ T : ℝ) (E : I → ℝ)
    (S : I → I → ℂ) (hω : ∀ n m, n ≠ m → E m - E n ≠ 0) (hħ : ħ ≠ 0) :
    thermalRateWindow Qr β ħ T E S =
      Qr⁻¹ * (∑ n, ∑ m ∈ Finset.univ.erase n,
        Complex.exp (-(β * (E n + E m)) / 2) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ) *
          ((Complex.exp (Complex.I * (((E m - E n) / ħ : ℝ) : ℂ) * T) - 1) /
            (Complex.I * (((E m - E n) / ħ : ℝ) : ℂ)))) := by
  unfold thermalRateWindow
  rw [intervalIntegral_eq16Correlation β ħ T E S hω hħ]

/-- The normalized spectral integral over a zero time window is zero. -/
theorem thermalRateWindow_zero (Qr : ℂ) (β ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) :
    thermalRateWindow Qr β ħ 0 E S = 0 := by
  unfold thermalRateWindow
  simp

end Qatlib.Papers.ThermalRate98.MainResults
