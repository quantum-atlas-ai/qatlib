/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FastFwdDissip24.MainResults.SourceModel
public import Mathlib.Tactic.Positivity

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.FastFwdDissip24.MainResults.SourceChecks

open Qatlib.Papers.FastFwdDissip24.MainResults

/-- The legacy QLSA query formula is positive at accuracy one when its condition proxy is positive. -/
theorem query_at_one {κ : ℝ} (hκ : 0 < κ) : 0 < qlsaQueries κ (1 / 2) := by
  unfold qlsaQueries
  norm_num
  exact mul_pos hκ (Real.log_pos (by norm_num))

/-- A multiple of log one cannot bound the positive legacy QLSA cost at accuracy one. -/
theorem log_one_obstruction {κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ C : ℝ, 0 < C ∧ qlsaQueries κ (1 / 2) ≤ C * Real.log (1 / (1 : ℝ)) := by
  rintro ⟨C, _, h⟩
  have hp := query_at_one hκ
  norm_num at h
  exact (not_le_of_gt hp) h

end Qatlib.Papers.FastFwdDissip24.MainResults.SourceChecks
