/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgForm09.MainResults.Model.Formula
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

set_option backward.isDefEq.respectTransparency false

/-!
# The coherent word model used in Theorems 1.9 and 1.11

Both main theorems of arXiv:0907.1622v1 state the running time of an algorithm that has
unit-cost coherent access to a preprocessed input string (the paper's "preprocessing"
model, Section 1 and Section 4). The library's `SourceWord`/`sourceFunctionQ` model of
`QuantumAlgorithm.Concepts.GramQueryCore.LowerBoundTools.SourceResidualModels` is exactly
this model: a word is a list of input-independent unitaries (`Sum.inl U`) interleaved with
forward or inverse queries to the alphabet oracle (`Sum.inr b`), and success is measured
on the clean start state with the tag register holding the answer.

`WordComputes` states the success predicate (probability `≥ 2/3` of reading the function
value) for a fixed word and function. The query bound of the theorems is the count of
`Sum.inr` entries (`sourceWordCalls`), and the running time is the word length
(`List.length`), matching the paper's `O(Adv±)` queries and
`Adv±·(log Adv±)^{O(1)}` time with a fixed input-independent preprocessing.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgForm09.MainResults

open Matrix
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators ENNReal

/-- `C` is a legal coherent word over the source space of `n = Fintype.card I` bits with
alphabet `{0,1}` (encoded in `Fin 2`), and, started from the clean state, it outputs
`f x` with probability at least `2/3` on every input `x`. This is the success predicate
inside `sourceFunctionQ`, exposed so the main theorems can speak about the word's length. -/
def WordComputes {I : Type} [Fintype I] [DecidableEq I] {r : ℕ} (hr : 0 < r)
    (f : (I → Bool) → Bool)
    (C : SourceWord (SourceSpace (Fintype.card I) 1 (Option Bool) r)) : Prop :=
  sourceWordLegal C ∧
    ∀ x : I → Bool,
      MeasureProb
        (sourceWordMatrix (sourceAlphabetOracle (bitInput I) x) C *ᵥ
          sourceClean (Fintype.card I) 1 r hr false (Ket none))
        (Finset.univ.filter
          (fun p : SourceSpace (Fintype.card I) 1 (Option Bool) r => p.2.1.2 = some (f x))) ≥
        2 / 3

end Qatlib.Papers.SpanProgForm09.MainResults
