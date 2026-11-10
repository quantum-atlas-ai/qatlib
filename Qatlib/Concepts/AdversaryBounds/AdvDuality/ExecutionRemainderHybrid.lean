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

theorem toObserved_quantum {D : ℕ} (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ))
    (t : HybridLeaf D Bool) :
    (t.quantum U q g m out).toObserved = (t.toObserved).prepend U q g m out := rfl
end Qatlib.Concepts.AdversaryBounds.AdvDuality
