/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedStat

/-!
# Corrected single-target quantum query lower bound

Proves `theorem7Corrected` by combining the quadratic fixed-query inequality with the separate
zero-query restriction. The result is stated as `Theorem7Corrected` with an explicit integer
floor. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `theorem7Corrected`: Establishes `Theorem7Corrected`, the floor lower bound with constant
  `Real.sin (Real.pi / 8)` for average single-target success at least one half.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u v

/-- Establishes `Theorem7Corrected`, the floor lower bound with constant `Real.sin (Real.pi /
8)` for average single-target success at least one half. See [BoyerEtAl1998]. -/
theorem theorem7Corrected : Theorem7Corrected.{u, v} := by
  intro C Y _ _ _ _ _ U V f ψ hψ r hagree hsuccess
  apply floor_bound_of_quadratic (Fintype.card Y) r
  · exact fixed_query_quadratic_bound U V f ψ hψ r hagree hsuccess
  · intro hr
    subst r
    exact zero_query_card_le_two (f 0) ψ hψ hsuccess

end Qatlib.Concepts.SearchStopping.QueryLowerBound
