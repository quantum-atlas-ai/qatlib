/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Gamma-function modulus for the inverse schedule

This module proves a squared-modulus identity for the gamma function on the nonzero imaginary
axis. It applies that identity to the coefficient `inverseScheduleCoeff` used in the
inverse-schedule formulas of [KadowakiNishimori1998].

## Main statements

* `gamma_imag_norm_sq`: evaluates `‖Γ(iy)‖²` for nonzero real `y`.
* `inverseScheduleCoeff_norm_sq`: evaluates the coefficient norm as a ratio of hyperbolic sines.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Complex

/-- For nonzero real `y`, the squared norm of `Γ(iy)` equals `π / (y * sinh (πy))`. -/
theorem gamma_imag_norm_sq (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (I * (y : ℂ))‖ ^ 2
      = Real.pi / (y * Real.sinh (Real.pi * y)) := by
  have hz : I * (y : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hy him
  have hne : (-(I * (y : ℂ))) ≠ 0 := neg_ne_zero.mpr hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (I * (y : ℂ))
  have hstep : Complex.Gamma (1 - I * (y : ℂ))
      = (-(I * (y : ℂ))) * Complex.Gamma (-(I * (y : ℂ))) := by
    have h1 : (1 : ℂ) - I * (y : ℂ) = (-(I * (y : ℂ))) + 1 := by ring
    rw [h1, Complex.Gamma_add_one _ hne]
  have hsin : Complex.sin ((Real.pi : ℂ) * (I * (y : ℂ)))
      = ((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I := by
    have harg : (Real.pi : ℂ) * (I * (y : ℂ)) = ((Real.pi * y : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, Complex.sin_mul_I, Complex.ofReal_sinh]
  have h0 : Complex.Gamma (I * (y : ℂ))
        * ((-(I * (y : ℂ))) * Complex.Gamma (-(I * (y : ℂ))))
      = (Real.pi : ℂ) / (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) := by
    rw [← hstep, hrefl, hsin]

  have hIden : (I : ℂ) * (-(I * (y : ℂ))) = (y : ℂ) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
    ring
  have hfin : (Real.pi : ℂ) / (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) / (-(I * (y : ℂ)))
      = ((Real.pi / (y * Real.sinh (Real.pi * y)) : ℝ) : ℂ) := by
    rw [div_div]
    have hden : (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) * (-(I * (y : ℂ)))
        = ((Real.sinh (Real.pi * y) : ℝ) : ℂ) * (y : ℂ) := by
      rw [mul_assoc, hIden]
    rw [hden]
    push_cast
    ring
  have hkey : Complex.Gamma (I * (y : ℂ)) * Complex.Gamma (-(I * (y : ℂ)))
      = ((Real.pi / (y * Real.sinh (Real.pi * y)) : ℝ) : ℂ) := by
    have hmul : Complex.Gamma (I * (y : ℂ)) * Complex.Gamma (-(I * (y : ℂ)))
          * (-(I * (y : ℂ)))
        = (Real.pi : ℂ) / (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) := by
      have h' : (-(I * (y : ℂ)))
            * (Complex.Gamma (I * (y : ℂ)) * Complex.Gamma (-(I * (y : ℂ))))
          = (Real.pi : ℂ) / (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) := by
        rw [← h0]
        ring
      rw [mul_comm] at h'
      exact h'
    have hdiv : Complex.Gamma (I * (y : ℂ)) * Complex.Gamma (-(I * (y : ℂ)))
        = (Real.pi : ℂ) / (((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I) / (-(I * (y : ℂ))) :=
      (eq_div_iff hne).mpr hmul
    rw [hdiv, hfin]
  have hconj : (starRingEnd ℂ) (Complex.Gamma (I * (y : ℂ)))
      = Complex.Gamma (-(I * (y : ℂ))) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp
  rw [Complex.sq_norm]
  have hns : Complex.normSq (Complex.Gamma (I * (y : ℂ)))
      = (Complex.Gamma (I * (y : ℂ)) * Complex.Gamma (-(I * (y : ℂ)))).re := by
    have h := Complex.normSq_eq_conj_mul_self (z := Complex.Gamma (I * (y : ℂ)))
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re] at hre
    rw [hre, hconj, mul_comm]
  rw [hns, hkey, Complex.ofReal_re]

/-- For positive `h` and `c`, the squared norm of `inverseScheduleCoeff h c` equals `sinh (πc) /
sinh (2πc)` [KadowakiNishimori1998]. -/
theorem inverseScheduleCoeff_norm_sq (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    ‖inverseScheduleCoeff h c‖ ^ 2
      = Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c) := by
  have hbase : ((2 : ℂ) * (h : ℂ)) = ((2 * h : ℝ) : ℂ) := by push_cast; ring
  have hnormc : ‖((2 : ℂ) * (h : ℂ)) ^ (-(I * (c : ℂ)))‖ = 1 := by
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * h)]
    simp
  have hnorm_K : ‖inverseScheduleCoeff h c‖
      = Real.sqrt 2 * (‖Complex.Gamma (I * 2 * (c : ℂ))‖ / ‖Complex.Gamma (I * (c : ℂ))‖) := by
    unfold inverseScheduleCoeff
    rw [norm_div, norm_mul, norm_mul, hnormc, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
    ring
  have hG2 := gamma_imag_norm_sq (2 * c) (by positivity)
  have hG1 := gamma_imag_norm_sq c (ne_of_gt hc)
  have hs2 : Real.sinh (Real.pi * (2 * c)) ≠ 0 :=
    (Real.sinh_ne_zero).mpr (ne_of_gt (by positivity))
  have hs1 : Real.sinh (Real.pi * c) ≠ 0 :=
    (Real.sinh_ne_zero).mpr (ne_of_gt (by positivity))
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hnorm_K]
  have hsq2 : (Real.sqrt 2 * (‖Complex.Gamma (I * 2 * (c : ℂ))‖ / ‖Complex.Gamma (I * (c : ℂ))‖)) ^ 2
      = 2 * (‖Complex.Gamma (I * 2 * (c : ℂ))‖ ^ 2 / ‖Complex.Gamma (I * (c : ℂ))‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have harg2 : I * 2 * (c : ℂ) = I * ((2 * c : ℝ) : ℂ) := by push_cast; ring
  rw [hsq2, harg2, hG2, hG1]
  have hA : Real.sinh (Real.pi * (2 * c)) = Real.sinh (2 * Real.pi * c) := by
    rw [show Real.pi * (2 * c) = 2 * Real.pi * c by ring]
  have hsin2 : Real.sinh (2 * Real.pi * c)
      = 2 * Real.sinh (Real.pi * c) * Real.cosh (Real.pi * c) := by
    rw [show 2 * Real.pi * c = 2 * (Real.pi * c) by ring]
    exact Real.sinh_two_mul (Real.pi * c)
  rw [hA, hsin2]
  have hc1 : Real.sinh (Real.pi * c) ≠ 0 := hs1
  have hch : Real.cosh (Real.pi * c) ≠ 0 := ne_of_gt (by positivity)
  have hcne : c ≠ 0 := ne_of_gt hc
  have h2cne : (2 : ℝ) * c ≠ 0 := by positivity
  field_simp

end Qatlib.Papers.TITCMTReport98.MainResults
