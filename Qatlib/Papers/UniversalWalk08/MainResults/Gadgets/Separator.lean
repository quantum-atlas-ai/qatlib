/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.Filter
set_option warningAsError false

namespace Qatlib.Papers.UniversalWalk08.MainResults.Gadgets

open Complex
open Qatlib.Papers.UniversalWalk08.MainResults.Filter

set_option autoImplicit false

theorem cos_neg_pi_div_four : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by
  rw [Real.cos_neg, Real.cos_pi_div_four]

noncomputable def separatorCorrection (k : ℝ) : ℂ :=
  Complex.I * ((Real.cos k + Real.cos (3 * k) : ℝ) : ℂ) /
    ((Real.sin k + 2 * Real.sin (2 * k) + Real.sin (3 * k) -
      Real.sin (5 * k) : ℝ) : ℂ)

noncomputable def separatorTrans (k : ℝ) : ℂ :=
  (1 + separatorCorrection k)⁻¹

theorem cos_neg_three_pi_div_four :
    Real.cos (-(3 * Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.cos_neg, show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four]

theorem separatorTrans_working_momentum : separatorTrans (-(Real.pi / 4)) = 1 := by
  unfold separatorTrans separatorCorrection
  have hcos3 : Real.cos (3 * (-(Real.pi / 4))) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * (-(Real.pi / 4)) = -(3 * Real.pi / 4) by ring,
      cos_neg_three_pi_div_four]
  have hsum : (Real.cos (-(Real.pi / 4)) + Real.cos (3 * (-(Real.pi / 4))) : ℝ) = 0 := by
    rw [hcos3, show Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 from
      cos_neg_pi_div_four]
    ring
  rw [hsum]
  simp

theorem cos_neg_nine_pi_div_four :
    Real.cos (-(9 * Real.pi / 4)) = Real.sqrt 2 / 2 := by
  have h : -(9 * Real.pi / 4) = -(Real.pi / 4) + -(2 * Real.pi) := by ring
  rw [h, Real.cos_add, cos_neg_pi_div_four, sin_neg_pi_div_four,
    Real.cos_neg, Real.sin_neg, Real.cos_two_pi, Real.sin_two_pi]
  ring

theorem separatorTrans_second_momentum :
    separatorTrans (-(3 * Real.pi / 4)) = 1 := by
  unfold separatorTrans separatorCorrection
  have hcos3 : Real.cos (3 * (-(3 * Real.pi / 4))) = Real.sqrt 2 / 2 := by
    rw [show 3 * (-(3 * Real.pi / 4)) = -(9 * Real.pi / 4) by ring,
      cos_neg_nine_pi_div_four]
  have hsum : (Real.cos (-(3 * Real.pi / 4)) +
      Real.cos (3 * (-(3 * Real.pi / 4))) : ℝ) = 0 := by
    rw [hcos3, cos_neg_three_pi_div_four]
    ring
  rw [hsum]
  simp

theorem separatorTrans_third_momentum :
    separatorTrans (-(Real.pi / 2)) = 1 := by
  unfold separatorTrans separatorCorrection
  have hcos3 : Real.cos (3 * (-(Real.pi / 2))) = 0 := by
    rw [show 3 * (-(Real.pi / 2)) = -(3 * Real.pi / 2) by ring,
      cos_neg_three_pi_div_two]
  have h1 : Real.cos (-(Real.pi / 2)) = 0 := cos_neg_pi_div_two
  rw [hcos3, h1]
  simp

end Qatlib.Papers.UniversalWalk08.MainResults.Gadgets
