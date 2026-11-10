/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

theorem isTriangle_swap {V : Type*} (G : SimpleGraph V) (a b c : V) :
    IsTriangle G a b c ↔ IsTriangle G b a c := by
  unfold IsTriangle
  constructor
  · rintro ⟨hab, hbc, hac, eab, ebc, eac⟩
    exact ⟨Ne.symm hab, hac, hbc, G.adj_symm eab, eac, ebc⟩
  · rintro ⟨hba, hac, hbc, eba, eac, ebc⟩
    exact ⟨Ne.symm hba, hbc, hac, G.adj_symm eba, ebc, eac⟩

end Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding
