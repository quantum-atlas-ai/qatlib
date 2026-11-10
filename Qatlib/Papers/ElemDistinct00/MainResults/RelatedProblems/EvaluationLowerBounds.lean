/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

theorem collisionCount_le_sq (N : ℕ) (f : Fin N → Fin N) :
    collisionCount f ≤ N * N := by
  unfold collisionCount
  calc (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ f p.1 = f p.2).card
      ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
    _ = N * N := by simp [Fintype.card_prod]

end Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems
