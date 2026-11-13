/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Lemma 2: the `{5,5,4}` constellation extends only to product triples

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 2, p. 8:

> The product constellation `{5,5,4}⊗₆` extends to a triple of MU bases only by adding
> product states.

Equivalently (the form used in the paper): any MU triple of `C² ⊗ C³` that contains the
constellation `{5,5,4}⊗₆` is a triple of MU *product* bases.  This is exactly what
Theorem 2 needs: it turns the constellation into a triple of MU product bases, which
Theorem 1 forbids.

**Source proof route** (pp. 8–10, Eqs. (29)–(38)).
1. By Lemma 3 the two MU bases belong to `P0`–`P3`; by Lemma 4 the pairs `P2`, `P3` admit
   no further product state (a complete qutrit MU set / no state MU to `B_z,B_x,{|r̂_σ j_x⟩}`).
2. Hence the five-state parts are `P0` or `P1`, and each of the four states in `S` has a
   qubit factor equal to `|0_y⟩` or `|1_y⟩`, giving the forms `S1` (Eq. (30)) or `S2`
   (Eq. (31)).
3. For `S1`, the two orthogonal completing states are automatically product (Eq. (32)).
   For `S2`, a completing state `|ψ₂⟩ = α|0_y,A^⊥⊥⟩ + β|1_y,B^⊥⊥⟩` (Eq. (33)) is entangled
   unless `|A^⊥⊥⟩ = |B^⊥⊥⟩`; the MU conditions (34) become `αβ̄ω_Jω̄'_J + ᾱβω̄_Jω'_J = 0`
   (Eq. (36)); `J = 0` forces `αβ̄ + ᾱβ = 0` (Eq. (37)); substituting yields
   `αβ̄(ω_Jω̄'_J − ω̄_Jω'_J) = 0` (Eq. (38)), impossible for distinct `|A^⊥⊥⟩ ≠ |B^⊥⊥⟩`;
   hence `α = 0` or `β = 0` and `|ψ₂⟩` is a product state.

**Status.**  The statement is registered as a `Prop`-valued definition; the proof is not
formalised.  The argument needs the Lemma 3 pair classification and the
Lemma 4 local-unbiasedness reduction together with a formal treatment of third roots of
unity (`ω = e^{2πi/3}`, `ω̄`, `ω_J, ω'_J`) and the qubit/qutrit basis normal forms.  Those
pieces are stated here (`Lemma3PairClassification`, `Lemma4LocalFactorization`) but the
contradiction (37)–(38) and the `S1`/`S2` case analysis are not yet assembled.
These steps involve Eq. (33)'s two-parameter family, the root-of-unity identities
in (36)–(38) over `ℂ`, and the `ProductModel` factorization lemmas.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel
open Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

/-- **Lemma 2** (arXiv:1203.6887v2, p. 8).  Any MU triple of `C² ⊗ C³` extending the
product constellation `{5,5,4}⊗₆` consists entirely of product states, i.e. is a triple of
MU product bases.  Registered as a `Prop`-valued definition; the proof is not
formalised. -/
def lemma2_extension_is_product
    (C : Constellation554)
    (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3))
    (hT : IsMuTriple T)
    (hcont : ContainsConstellationInTriple T C) : Prop :=
  ∀ r k, IsProductState (T r k)

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation
