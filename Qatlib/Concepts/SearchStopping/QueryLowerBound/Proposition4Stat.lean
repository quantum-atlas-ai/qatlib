/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

def Proposition4 : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E), ‖a‖ = 1 → ‖b‖ = 1 → ∀ (α β : ℂ),
      ‖α‖ ^ 2 + ‖β‖ ^ 2 - 2 * ‖α‖ * ‖β‖ ≤ ‖α • a - β • b‖ ^ 2

end Qatlib.Concepts.SearchStopping.QueryLowerBound
