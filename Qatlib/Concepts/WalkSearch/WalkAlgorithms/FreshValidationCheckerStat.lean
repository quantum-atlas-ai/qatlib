/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

def FreshValidationChecker : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ),
    triCheckSpecFreshValidation adj U kcs ncs r' c₀
end Qatlib.Concepts.WalkSearch.WalkAlgorithms
