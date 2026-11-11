/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Real reflections and a detection probability bound

This module defines the real-Hilbert-space hyperplane reflection `reflection` and proves its
basic orthogonality and involution identities. It also verifies the scalar lower bound for a
marked-detection success expression appearing in [Itakura2005].

## Main statements

* `reflection_involutive`: A reflection with a unit normal is involutive.
* `reflection_reflection_orthogonal`: Two reflections fix a vector orthogonal to both normals.
* `detection_success_probability`: The detection expression is at least `12 / 25` and hence `1 /
  1000`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace Qatlib.Papers.CommuteTest05.WalkDetect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The map `x ↦ x - (2 * inner ℝ a x) • a`, which is reflection across the hyperplane
orthogonal to `a` when `a` is a unit vector. -/
def reflection (a x : E) : E := x - (2 * inner ℝ a x) • a

/-- The reflection `reflection a` fixes every vector orthogonal to `a`, as used in the
walk-reflection analysis of [Itakura2005]. -/
theorem reflection_orthogonal (a x : E) (h : inner ℝ a x = 0) :
    reflection a x = x := by
  simp [reflection, h]

/-- If `a` has squared norm one, applying `reflection a` twice fixes every vector, as used in
[Itakura2005]. -/
theorem reflection_involutive (a x : E) (ha : inner ℝ a a = 1) :
    reflection a (reflection a x) = x := by
  unfold reflection
  have hI : inner ℝ a (x - (2 * inner ℝ a x) • a) = -inner ℝ a x := by
    rw [inner_sub_right, inner_smul_right, ha, mul_one]
    ring
  rw [hI]
  rw [show (2 * -inner ℝ a x) = -(2 * inner ℝ a x) by ring, neg_smul]
  abel

/-- The composition of reflections with normals `a` and `b` fixes every vector orthogonal to
both normals. -/
theorem reflection_reflection_orthogonal (a b x : E)
    (ha : inner ℝ a x = 0) (hb : inner ℝ b x = 0) :
    reflection b (reflection a x) = x := by
  rw [reflection_orthogonal a x ha, reflection_orthogonal b x hb]

/-- For nonnegative `ε`, the expression `ε + 12 / 25 * (1 - ε)` is at least both `12 / 25` and
`1 / 1000`. This is the scalar success bound associated with the detection analysis in
[Itakura2005]. -/
theorem detection_success_probability (ε : ℝ) (hε : 0 ≤ ε) :
    12 / 25 ≤ ε + 12 / 25 * (1 - ε) ∧
      (1 / 1000 : ℝ) ≤ ε + 12 / 25 * (1 - ε) := by
  constructor <;> nlinarith

end Qatlib.Papers.CommuteTest05.WalkDetect
