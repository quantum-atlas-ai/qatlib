/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainderDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedFeedbackConsumer
import Mathlib.Tactic.FinCases

/-!
# Hybrid leaves and observed quantum steps

This module proves that the conversion `HybridLeaf.toObserved` commutes with prepending a
quantum operation and its resource data. The result connects hybrid execution records to
observed Kraus leaves in the quantum operation formalism of [Watrous2018].

## Main statements

* `toObserved_quantum`: converting a leaf after a quantum update gives the corresponding
  observed leaf update.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped ENNReal
variable {α : Type}

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
variable {β : Type}
variable {D : ℕ} {A : Type}
variable {α : Type}
variable {A : Type}
open Classical
open scoped ComplexOrder

/-- Converting a quantum updated hybrid leaf to an observed leaf equals prepending the same
operation and resource data after conversion. -/
theorem toObserved_quantum {D : ℕ} (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ))
    (t : HybridLeaf D Bool) :
    (t.quantum U q g m out).toObserved = (t.toObserved).prepend U q g m out := rfl
end Qatlib.Concepts.AdversaryBounds.AdvDuality
