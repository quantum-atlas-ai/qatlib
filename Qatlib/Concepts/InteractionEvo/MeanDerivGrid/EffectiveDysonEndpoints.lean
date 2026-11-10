/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectivePrimitiveExecution
import Qatlib.Concepts.InteractionEvo.SegmentProduct.EffectiveProductPerturbationHami
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorHami
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveInteractionGateRateHami
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveRobustOAA
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.EffCosts

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix

theorem effectiveMatrix_append (n : ℕ) (E : EffectiveEnvironment)
    (a b : List EffectiveStep) :
    effectiveMatrix ⟨n,a++b⟩ E = effectiveMatrix ⟨n,b⟩ E * effectiveMatrix ⟨n,a⟩ E := by
  simp [effectiveMatrix,List.prod_append]

theorem effectiveCounts_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveQueries ⟨n,a++b⟩ = effectiveQueries ⟨n,a⟩+effectiveQueries ⟨n,b⟩ ∧
    effectiveGates ⟨n,a++b⟩ = effectiveGates ⟨n,a⟩+effectiveGates ⟨n,b⟩ ∧
    effectivePostselects ⟨n,a++b⟩ = effectivePostselects ⟨n,a⟩+effectivePostselects ⟨n,b⟩ := by
  simp [effectiveQueries,effectiveGates,effectivePostselects,List.filter_append]

theorem effectiveSlotQueries_append (n j : ℕ) (a b : List EffectiveStep) :
    effectiveSlotQueries ⟨n,a++b⟩ j = effectiveSlotQueries ⟨n,a⟩ j+effectiveSlotQueries ⟨n,b⟩ j := by
  simp [effectiveSlotQueries,List.filter_append]

theorem effectiveLegal_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveLegal ⟨n,a++b⟩ ↔ effectiveLegal ⟨n,a⟩ ∧ effectiveLegal ⟨n,b⟩ := by
  simp [effectiveLegal,or_imp,forall_and]

theorem effectiveCoherent_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveCoherent ⟨n,a++b⟩ ↔ effectiveCoherent ⟨n,a⟩ ∧ effectiveCoherent ⟨n,b⟩ := by
  simp [effectiveCoherent,not_or,forall_and]

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
