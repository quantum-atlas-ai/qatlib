/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Lemma 1: classification of MU product triples in `C² ⊗ C³`

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 1, p. 3, Eq. (1):

> Any triple of MU product bases in the space `C² ⊗ C³` is equivalent to either
> `T0 = {|j_z, J_z⟩; |j_x, J_x⟩; |j_y, J_y⟩}` or
> `T1 = {|j_z, J_z⟩; |j_x, J_x⟩; |0_y, J_y⟩, |1_y, J_w⟩}`,
> where `j = 0,1` and `J = 0,1,2`.

The equivalence used is that of [19]: a common unitary (or anti-unitary) acting on all
bases that respects the product structure, arbitrary re-ordering of bases, permutations of
states inside a basis, and multiplication of states by arbitrary phases, with the modulus
of inner products preserved.  `ProductEquiv` in `ProductModel` encodes the unitary,
permutation and phase part; the anti-unitary global conjugation is *not* modelled in the
Lean witness relation (recorded as a gap below).

**Source proof route.**  The result is imported from the exhaustive classification of
Kalev–Henini–Gour [19] (obtained by computer-algebraic search); the paper uses it as the
starting point and does not reprove it.  The Lean statement records the two canonical
families (T0 fully direct; T1 with a direct first and second basis but an indirect third
basis splitting into the `|0_y⟩`-sector `{|J_y⟩}` and the `|1_y⟩`-sector `{|J_w⟩}`) and the
covering of every MU product triple up to `ProductEquiv`.

**Status.**  The statement is registered as a `Prop`-valued definition; the proof is not
formalised.  A full proof needs (i) an exhaustive computer-algebraic
enumeration of product triples in `C² ⊗ C³`, and (ii) a formal equivalence-reduction
argument.  The available Frozen development
`Mub6Maximum.ThreeBasis.bases_isFamily` only certifies a
single explicit T0-type family (`covered_by`, restricted).  Candidate reuse: the concrete
Hadamard/qutrit tables in
`Mub6Maximum.ThreeBasis.MUBProductBases`.  Suggested route
for a successor: formalise the `C²⊗C³` product-basis normal form, enumerate the 48
pair-completions of [14], and dispatch T0/T1 by `fin_cases` + exact Gram computations.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma1Classification

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-- **Lemma 1** (arXiv:1203.6887v2, p. 3, Eq. (1)).  There exist two MU product triples
`T0` and `T1` of `C² ⊗ C³`: `T0` consists of three direct product bases (`|j_z,J_z⟩`,
`|j_x,J_x⟩`, `|j_y,J_y⟩`), while `T1` has direct first and second bases and an indirect third
basis splitting the `|0_y⟩` and `|1_y⟩` sectors between the qutrit bases `{|J_y⟩}` and
`{|J_w⟩}`.  Every MU product triple is equivalent (`ProductEquiv`) to `T0` or to `T1`.
Registered as a `Prop`-valued definition; the proof is not formalised. -/
def lemma1_classification : Prop :=
  ∃ (T0 T1 : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)),
    IsMuProductTriple T0 ∧ IsMuProductTriple T1 ∧
    (∀ r, IsDirectProductBasis (T0 r)) ∧
    IsDirectProductBasis (T1 0) ∧ IsDirectProductBasis (T1 1) ∧
    IsIndirectBasis (T1 2) ∧
    (∀ (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)),
      IsMuProductTriple T → ProductEquiv T T0 ∨ ProductEquiv T T1)

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma1Classification
