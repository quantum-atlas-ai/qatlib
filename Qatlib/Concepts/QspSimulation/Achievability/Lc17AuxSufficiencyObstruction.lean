/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Two-phase amplitude formulas

This module computes the real and imaginary parts of `wordAmp [a, b] x` explicitly. These
formulas describe the two-phase case of the quantum signal processing word model that underlies
the Hamiltonian simulation construction of [LowChuang2017].

The real part is a quadratic expression in `x` with coefficients `Real.cos (a + b)` and
`Real.cos (a - b)` on `[-1, 1]`. The imaginary part factors as `Real.sqrt (1 - x^2) * x` times
the sum of those cosines, providing concrete identities for examining amplitude constraints.

## Main statements

* `wordAmp_two_re` evaluates the real part for `x` in `[-1, 1]`.
* `wordAmp_two_im` gives the factored imaginary part for every real `x`.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial

/-- For `x` in `[-1, 1]`, the real part of the two-phase amplitude is `x^2 * cos (a + b) - (1 -
x^2) * cos (a - b)`. -/
theorem wordAmp_two_re (a b x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (wordAmp [a,b] x).re = x^2 * Real.cos (a+b) - (1-x^2) * Real.cos (a-b) := by
  have hs : (Real.sqrt (1-x^2)) ^ 2 = 1-x^2 := Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  simp only [wordAmp, lcHad, qspWord_cons, qspWord_nil, mul_one,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp [SignalMatrix, PhaseRotation, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im, Real.cos_add, Real.cos_sub]
  ring_nf
  simp only [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), hs]
  ring

/-- The imaginary part of the two-phase amplitude is `sqrt (1 - x^2) * x * (cos (a + b) + cos (a
- b))` for every real `x`. -/
theorem wordAmp_two_im (a b x : ℝ) :
    (wordAmp [a,b] x).im = Real.sqrt (1-x^2) * x *
      (Real.cos (a+b) + Real.cos (a-b)) := by
  simp only [wordAmp, lcHad, qspWord_cons, qspWord_nil, mul_one,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp [SignalMatrix, PhaseRotation, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im, Real.cos_add, Real.cos_sub]
  ring_nf
  rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  ring

end Qatlib.Concepts.QspSimulation.Achievability
