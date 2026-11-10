/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.Group
import Qatlib.Papers.SemidirectHSP07.MainResults.CommutatorStructure
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

theorem classOne_isSolvable (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    Group.IsSolvable (SDG p r φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (SDG p r φ) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_SDG_prime_pow p r hp φ]
      exact pow_ne_zero _ hp.ne_zero)
  haveI : Group.IsNilpotent (SDG p r φ) := (isPGroup_SDG p r hp φ).isNilpotent
  infer_instance

theorem normal_of_contains_commutator (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ)
    (H : Subgroup (SDG p r φ))
    (hH : Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2)) ≤ H) : H.Normal :=
  Subgroup.Normal.of_commutator_le (SDG p r φ) (H := H)
    (le_trans (classOne_commutator_le p r hp hr φ hφ) hH)

end Qatlib.Papers.SemidirectHSP07.MainResults
