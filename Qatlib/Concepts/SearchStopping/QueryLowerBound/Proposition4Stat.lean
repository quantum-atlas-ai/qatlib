/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Statement of a scaled unit-vector distance bound

Defines `Proposition4`, a lower bound for the squared distance between complex scalar multiples
of unit vectors. The lower bound is the squared difference of the scalar norms. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Proposition4`: The proposition that unit vectors `a` and `b` satisfy `‖α‖ ^ 2 + ‖β‖ ^ 2 - 2 *
  ‖α‖ * ‖β‖ ≤ ‖α • a - β • b‖ ^ 2` for all complex scalars.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

/-- The proposition that unit vectors `a` and `b` satisfy `‖α‖ ^ 2 + ‖β‖ ^ 2 - 2 * ‖α‖ * ‖β‖ ≤
‖α • a - β • b‖ ^ 2` for all complex scalars. -/
def Proposition4 : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E), ‖a‖ = 1 → ‖b‖ = 1 → ∀ (α β : ℂ),
      ‖α‖ ^ 2 + ‖β‖ ^ 2 - 2 * ‖α‖ * ‖β‖ ≤ ‖α • a - β • b‖ ^ 2

end Qatlib.Concepts.SearchStopping.QueryLowerBound
