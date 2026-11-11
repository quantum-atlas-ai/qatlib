/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Polynomial overhead bounds for singular-value estimation

Shared cost vocabulary used by the SVE constructions and data-structure bounds
of QGradDescent17. The cost relation and its reflexivity estimate retain the
paper modules' original statements.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QGradDescent17.MainResults.SVE

/-- Coarse soft-`O` encoding: `f` is at most a polynomial in `1 + g`. -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

end Qatlib.Papers.QGradDescent17.MainResults.SVE
