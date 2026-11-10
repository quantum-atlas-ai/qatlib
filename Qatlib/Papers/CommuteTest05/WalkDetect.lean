/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace Qatlib.Papers.CommuteTest05.WalkDetect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def reflection (a x : E) : E := x - (2 * inner ℝ a x) • a

theorem reflection_orthogonal (a x : E) (h : inner ℝ a x = 0) :
    reflection a x = x := by
  simp [reflection, h]

theorem reflection_involutive (a x : E) (ha : inner ℝ a a = 1) :
    reflection a (reflection a x) = x := by
  unfold reflection
  have hI : inner ℝ a (x - (2 * inner ℝ a x) • a) = -inner ℝ a x := by
    rw [inner_sub_right, inner_smul_right, ha, mul_one]
    ring
  rw [hI]
  rw [show (2 * -inner ℝ a x) = -(2 * inner ℝ a x) by ring, neg_smul]
  abel

theorem reflection_reflection_orthogonal (a b x : E)
    (ha : inner ℝ a x = 0) (hb : inner ℝ b x = 0) :
    reflection b (reflection a x) = x := by
  rw [reflection_orthogonal a x ha, reflection_orthogonal b x hb]

theorem detection_success_probability (ε : ℝ) (hε : 0 ≤ ε) :
    12 / 25 ≤ ε + 12 / 25 * (1 - ε) ∧
      (1 / 1000 : ℝ) ≤ ε + 12 / 25 * (1 - ε) := by
  constructor <;> nlinarith

end Qatlib.Papers.CommuteTest05.WalkDetect
