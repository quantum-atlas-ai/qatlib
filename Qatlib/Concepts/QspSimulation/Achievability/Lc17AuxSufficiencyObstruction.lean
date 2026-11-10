/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial

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
