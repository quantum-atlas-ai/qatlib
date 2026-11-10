/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem18WeakDualityStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

theorem theorem18WeakDuality : Theorem18WeakDuality := by
  intro X _ _ κ _ _ input g α hα
  exact advNonneg_le_minimaxAlpha input g α hα
end Qatlib.Concepts.AdversaryBounds.AdvDuality
