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

/-!
# Concatenation laws for effective programs

This module proves composition laws for the matrix semantics and resource counts of effective
instruction lists. Legality and coherence of a concatenated program are equivalent to the
corresponding properties of both components. These laws support composition of simulation
programs in the framework of [LowWiebe2018].

## Main statements

* `effectiveMatrix_append`: concatenation corresponds to ordered matrix multiplication.
* `effectiveCounts_append`: query, gate, and postselection counts are additive.
* `effectiveLegal_append`: legality decomposes over concatenation.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.EffCosts

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix

/-- The matrix of instruction list `a ++ b` is the matrix of `b` multiplied by the matrix of
`a`. -/
theorem effectiveMatrix_append (n : ℕ) (E : EffectiveEnvironment)
    (a b : List EffectiveStep) :
    effectiveMatrix ⟨n,a++b⟩ E = effectiveMatrix ⟨n,b⟩ E * effectiveMatrix ⟨n,a⟩ E := by
  simp [effectiveMatrix,List.prod_append]

/-- Query, gate, and postselection counts are additive under concatenation of instruction lists
at a fixed width. -/
theorem effectiveCounts_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveQueries ⟨n,a++b⟩ = effectiveQueries ⟨n,a⟩+effectiveQueries ⟨n,b⟩ ∧
    effectiveGates ⟨n,a++b⟩ = effectiveGates ⟨n,a⟩+effectiveGates ⟨n,b⟩ ∧
    effectivePostselects ⟨n,a++b⟩ = effectivePostselects ⟨n,a⟩+effectivePostselects ⟨n,b⟩ := by
  simp [effectiveQueries,effectiveGates,effectivePostselects,List.filter_append]

/-- The query count for a fixed oracle slot is additive under concatenation. -/
theorem effectiveSlotQueries_append (n j : ℕ) (a b : List EffectiveStep) :
    effectiveSlotQueries ⟨n,a++b⟩ j = effectiveSlotQueries ⟨n,a⟩ j+effectiveSlotQueries ⟨n,b⟩ j := by
  simp [effectiveSlotQueries,List.filter_append]

/-- A concatenated instruction list is legal exactly when both component lists are legal at the
same width. -/
theorem effectiveLegal_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveLegal ⟨n,a++b⟩ ↔ effectiveLegal ⟨n,a⟩ ∧ effectiveLegal ⟨n,b⟩ := by
  simp [effectiveLegal,or_imp,forall_and]

/-- A concatenated instruction list is coherent exactly when both component lists contain no
postselection instructions. -/
theorem effectiveCoherent_append (n : ℕ) (a b : List EffectiveStep) :
    effectiveCoherent ⟨n,a++b⟩ ↔ effectiveCoherent ⟨n,a⟩ ∧ effectiveCoherent ⟨n,b⟩ := by
  simp [effectiveCoherent,not_or,forall_and]

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
