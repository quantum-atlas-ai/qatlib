/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Proposition4Stat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Linarith

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

theorem proposition4 : Proposition4.{u} := by
  intro E _ _ a b ha hb α β
  have reverse_triangle := abs_norm_sub_norm_le (α • a) (β • b)
  simp only [norm_smul, ha, hb, mul_one] at reverse_triangle
  have squared := (sq_le_sq₀ (abs_nonneg (‖α‖ - ‖β‖))
    (norm_nonneg (α • a - β • b))).2 reverse_triangle
  rw [sq_abs] at squared
  nlinarith [squared]

end Qatlib.Concepts.SearchStopping.QueryLowerBound
