/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentSeq.SeqAssoc.InstrumentCoarseGrainLaws

/-!
# Associativity of sequential instruments

This module proves `seq_associativity`: three sequential instruments have the same branch maps
and probabilities under the natural reassociation of their outcome triples. Their channels
obtained by forgetting all outcomes also agree.

The result records associativity at the level of branches, probabilities, and channels in the
instrument formalism [Wilde2017].

## Main statements

* `seq_associativity`: associativity of three sequential instruments under outcome
  reassociation.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.InstrumentSeq.SeqAssoc

/-- Sequential composition of three instruments is associative under reassociation of the
outcome triple, both for branch maps and probabilities; the channels obtained by forgetting
outcomes also agree. -/
theorem seq_associativity
    (O P Q : Type) [Fintype O] [Fintype P] [Fintype Q]
    (D E F G : ℕ) (I : Instrument O D E) (J : Instrument P E F)
    (K : Instrument Q F G) :
    (∀ (o : O) (p : P) (q : Q),
      ((I.seq J).seq K).branch ((o, p), q) =
        (I.seq (J.seq K)).branch (o, (p, q))) ∧
    (∀ (ρ : Operator D) (o : O) (p : P) (q : Q),
      instrumentProb ((I.seq J).seq K) ρ ((o, p), q) =
        instrumentProb (I.seq (J.seq K)) ρ (o, (p, q))) ∧
    ((I.seq J).seq K).forget.map = (I.seq (J.seq K)).forget.map := by
  classical
  refine ⟨fun _ _ _ => rfl, (fun _ _ _ _ => rfl), ?_⟩
  apply LinearMap.ext
  intro ρ
  simp only [Instrument.forget_apply, Instrument.seq, LinearMap.comp_apply,
    Fintype.sum_prod_type]

end Qatlib.Concepts.InstrumentSeq.SeqAssoc
