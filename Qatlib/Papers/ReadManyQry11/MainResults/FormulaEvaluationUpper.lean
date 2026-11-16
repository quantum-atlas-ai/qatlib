/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel

@[expose] public section


/-!
Four closed minimum comparisons retained from arXiv:1112.0548v1. These inequalities alone do not construct a formula query algorithm.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.ReadManyQry11.MainResults

open scoped BigOperators Real

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-- The first term of the paper's minimum never exceeds `n`. -/
theorem mainBound_le_n (n S G : ℕ) : mainBound n S G ≤ (n : ℝ) :=
  min_le_left _ _

/-- The paper's minimum is at most `√S`. -/
theorem mainBound_le_sqrt (n S G : ℕ) : mainBound n S G ≤ Real.sqrt (S : ℝ) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- The paper's minimum is at most `n^{1/2}G^{1/4}`. -/
theorem mainBound_le_pruning (n S G : ℕ) : mainBound n S G ≤ pruningBound n G :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- The paper's minimum is at most each of its three arguments, in the form used by the
three-algorithm proof of Theorem 2 (read all inputs / read-once algorithm / pruning). -/
theorem mainBound_le_all (n S G : ℕ) :
    mainBound n S G ≤ (n : ℝ) ∧ mainBound n S G ≤ Real.sqrt (S : ℝ) ∧
      mainBound n S G ≤ pruningBound n G :=
  ⟨mainBound_le_n n S G, mainBound_le_sqrt n S G, mainBound_le_pruning n S G⟩


end Qatlib.Papers.ReadManyQry11.MainResults
