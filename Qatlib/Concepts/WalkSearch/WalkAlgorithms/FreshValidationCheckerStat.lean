/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts

/-!
# Fresh validation checker contract

`FreshValidationChecker` requires `triCheckSpecFreshValidation` for all graph sizes, adjacency
relations, stored subsets, search primitives, and checker parameters. It packages the
specification used to connect a fresh graph checker to subsequent walk-search constructions.

For the surrounding setup, update, and checking perspective on quantum-walk search, see
[MagniezNayakRolandSantha2011].

## Main statements

* `FreshValidationChecker`: the universal fresh-checker specification.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- The universal fresh-checker contract requiring `triCheckSpecFreshValidation` for every
graph, stored subset, collision solver, noisy search primitive, and pair of checker
parameters. -/
def FreshValidationChecker : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ),
    triCheckSpecFreshValidation adj U kcs ncs r' c₀
end Qatlib.Concepts.WalkSearch.WalkAlgorithms
