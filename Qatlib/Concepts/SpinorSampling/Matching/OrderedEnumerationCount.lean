/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Ordered Enumeration Count

Ordered Enumeration Count constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

variable {S : Type} [DecidableEq S]

/-- Complete original `finset_ordered_enumeration_count` guarantee for `OrderedEnumerationCount`; all source hypotheses and output obligations are retained. -/
theorem finset_ordered_enumeration_count (A : Finset S) {k : ℕ}
    (hcard : A.card=k) :
    Fintype.card (Fin k ≃ A)=Nat.factorial k := by
  let e : Fin k ≃ A := (Equiv.cast (congrArg Fin hcard.symm)).trans A.equivFin.symm
  rw [Fintype.card_equiv e, Fintype.card_fin]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finset_ordered_enumeration_count
