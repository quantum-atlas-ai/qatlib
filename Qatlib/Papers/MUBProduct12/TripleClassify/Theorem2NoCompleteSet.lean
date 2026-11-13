/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Theorem 2: `{5,5,4}⊗₆` is not part of a complete set of seven MU bases

McNulty–Weigert, fixed arXiv:1203.6887v2, Theorem 2, p. 8:

> The product constellation `{5,5,4}⊗₆` cannot be part of a complete set of seven MU bases.

**Source proof route** (p. 8, one paragraph).  Suppose the constellation is part of a
complete set of seven MU bases.  By Lemma 2 the three bases hosting the two five-ray parts
and the four states extend to a triple of MU *product* bases.  Any state of any remaining
basis of the complete set is then MU to all three bases of that triple, so the triple is
extendable by a single MU vector — contradicting Theorem 1.

**Status.**  The statement is registered as a `Prop`-valued definition; the proof is not
formalised.  The reduction uses Lemma 2 (`lemma2_extension_is_product`)
and the general (all-triples) form of Theorem 1.  In this paper layer Theorem 1 is only
available for the canonical T0 triple
(`TripleClassify.Theorem1NoExtension.theorem1_canonical_T0`, a bridge to a Frozen result),
so the full reduction cannot yet be closed.  The mechanistic steps still to formalise are:
(i) select three distinct bases `rA, rB, rS` of the seven hosting the constellation and a
fourth distinct index `r4`; (ii) apply Lemma 2 on the restricted triple; (iii) feed one
vector `M r4 j` (MU to the triple by `IsCompleteMuSet.2`) into the general Theorem 1.
The reduction to the canonical T0 instance uses `IsMuTriple` restrictions and the
`ProductEquiv` classes of Lemma 1.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Theorem2NoCompleteSet

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel
open Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

/-- **Theorem 2** (arXiv:1203.6887v2, p. 8).  No complete set of seven MU bases of
`C² ⊗ C³` contains the product constellation `{5,5,4}⊗₆`.  Registered as a `Prop`-valued
definition; the proof is not formalised. -/
def theorem2_no_complete_set
    (C : Constellation554)
    (M : Fin 7 → Fin 6 → QState (Fin 2 × Fin 3))
    (hM : IsCompleteMuSet M) : Prop :=
  ¬ ContainsConstellationInSet M C

end Qatlib.Papers.MUBProduct12.TripleClassify.Theorem2NoCompleteSet
