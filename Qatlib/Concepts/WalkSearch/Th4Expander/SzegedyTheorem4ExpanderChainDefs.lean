/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

noncomputable def expanderStep (n d : ℕ) (adj : Fin n → Fin n → Bool) :
    Fin n → Fin n → ℝ :=
  fun i j => if adj i j then ((d : ℝ)⁻¹) else 0
end Qatlib.Concepts.WalkSearch.Th4Expander
