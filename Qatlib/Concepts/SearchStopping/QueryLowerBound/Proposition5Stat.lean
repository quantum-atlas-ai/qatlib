/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

def Proposition5 : Prop :=
  ∀ (r : ℕ) (x : Fin r → ℂ),
    (∑ i, ‖x i‖) ^ 2 ≤ (r : ℝ) * ∑ i, ‖x i‖ ^ 2

end Qatlib.Concepts.SearchStopping.QueryLowerBound
