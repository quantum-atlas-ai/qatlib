/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem18WeakDualityStat

/-!
# Weak duality for a nonnegative adversary bound

For finite Boolean input coordinates and strictly positive coordinate costs,
the nonnegative adversary quantity is at most the weighted minimax quantity.
The theorem instantiates the general weak-duality inequality for these data.

Adversary lower bounds originate in [Ambainis2002]; the broader state-conversion
framework is [Lee et al., quantum query complexity of state conversion][LeeEtAl2011].
The predicate used here specifically concerns the nonnegative adversary.
-/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- The nonnegative adversary is bounded above by the weighted minimax quantity.
For adversary-method background, see [Ambainis, quantum lower bounds][Ambainis2002]. -/
theorem theorem18WeakDuality : Theorem18WeakDuality := by
  intro X _ _ κ _ _ input g α hα
  exact advNonneg_le_minimaxAlpha input g α hα
end Qatlib.Concepts.AdversaryBounds.AdvDuality
