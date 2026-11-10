/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

noncomputable def expanderSearchLength (n : ℕ) (δ : ℝ) : ℕ :=
  Nat.ceil (1000 * Real.sqrt ((n : ℝ) / δ))
end Qatlib.Concepts.WalkSearch.Th4Expander
