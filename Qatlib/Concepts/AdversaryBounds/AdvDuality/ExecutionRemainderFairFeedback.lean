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
# Fair coin word weights

This module proves `wordWeight_cons`, the elementary recursion for the weight
`CoinCode.wordWeight` of a finite fair coin word. Prepending either Boolean multiplies the
weight by one half, as in the classical random choices used in quantum computation
[NielsenChuang2010].

## Main statements

* `wordWeight_cons`: one additional fair bit halves a word's weight.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped ENNReal
variable {α : Type}

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- Prepending either Boolean to a coin word multiplies its weight by one half. -/
@[simp] theorem wordWeight_cons (b : Bool) (w : List Bool) :
    wordWeight (b :: w) = (1 / 2 : ℝ) * wordWeight w := by
  simp only [wordWeight, List.length_cons, pow_succ']
end Qatlib.Concepts.AdversaryBounds.AdvDuality
