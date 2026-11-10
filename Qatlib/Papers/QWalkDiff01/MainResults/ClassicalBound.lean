/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

theorem classicalColumnProb_zero (n : ℕ) (γ : ℝ) :
    classicalColumnProb n γ 0 = Pi.single (0 : Fin (2 * n + 1)) 1 := by
  unfold classicalColumnProb
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

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
