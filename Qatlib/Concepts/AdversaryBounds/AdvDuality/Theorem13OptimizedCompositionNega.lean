/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem13OptimizedCompositionStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

theorem theorem13OptimizedComposition : Theorem13OptimizedComposition := by
  intro k X _ _ n hne g hnc f gin α hα β hβ
  exact advPlus_composition_ge k X n hne g hnc f gin α hα β hβ
end Qatlib.Concepts.AdversaryBounds.AdvDuality
