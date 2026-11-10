/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

def Theorem18WeakDuality : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (κ : Type) [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (hα : ∀ i, 0 < α i),
    advNonneg input g α ≤ minimaxAlpha input g α

end Qatlib.Concepts.AdversaryBounds.AdvDuality
