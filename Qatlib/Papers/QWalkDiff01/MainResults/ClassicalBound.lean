/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.Defs

/-!
# The classical column walk at time zero

`classicalColumnProb_zero` identifies the initial column vector with the unit mass at the left
root. When `n ≥ 1`, the right root differs from the left root, and its time-zero coordinate is
strictly less than `(1 / 2) ^ n`. The mathematical setting is described in
[ChildsFarhiGutmann2002].

## Main statements

* `classicalColumnProb_zero`: the initial column vector is `Pi.single 0 1`.
* `classical_propagation_bound_at_zero`: the right-root coordinate satisfies the stated bound at
  time zero.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- At time zero, the classical column evolution is the unit coordinate vector at column zero. -/
theorem classicalColumnProb_zero (n : ℕ) (γ : ℝ) :
    classicalColumnProb n γ 0 = Pi.single (0 : Fin (2 * n + 1)) 1 := by
  unfold classicalColumnProb
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

/-- For `n ≥ 1`, the right-root coordinate of the classical column evolution at time zero is
strictly less than `(1 / 2) ^ n`. See [ChildsFarhiGutmann2002]. -/
theorem classical_propagation_bound_at_zero (n : ℕ) (hn : 1 ≤ n) (γ : ℝ) :
    classicalColumnProb n γ 0 (rightRoot n) < (1 / 2 : ℝ) ^ n := by
  have hne : rightRoot n ≠ (0 : Fin (2 * n + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp [rightRoot] at hv
    omega
  have hzero : classicalColumnProb n γ 0 (rightRoot n) = 0 := by
    rw [classicalColumnProb_zero]
    simp [hne]
  rw [hzero]
  exact pow_pos (one_div_pos.mpr zero_lt_two) n

end Qatlib.Papers.QWalkDiff01.MainResults
