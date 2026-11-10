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

namespace Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

theorem elementDistinct_iff_not_hasCollision {X Z : Type*} (f : X → Z) :
    ElementDistinct f ↔ ¬ HasCollision f :=
  Iff.rfl

theorem not_hasCollision_fin_one (f : Fin 1 → ℤ) : ¬ HasCollision f := by
  rintro ⟨x, y, hxy, -⟩
  exact hxy (Subsingleton.elim x y)

end Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct
