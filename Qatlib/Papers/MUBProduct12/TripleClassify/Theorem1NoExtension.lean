/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Theorem 1: no single MU vector extends a triple of MU product bases

McNulty–Weigert, fixed arXiv:1203.6887v2, Theorem 1, pp. 3–4:

> No triple of MU product bases in dimension six can be extended by a single MU vector.

The paper reduces Theorem 1, via Lemma 1, to the two canonical triples T0 and T1 and
then analyses the 18 equations (4) (for T0) and the equations (5) (for T1) of p. 4.

**Reused result (exact FQN).**
`Mub6LocalT0.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth.CanonicalUnextendibilityRestricted.canonicalUnextendibilityRestricted`
is the *full* canonical T0 instance: for the explicit direct-product triple
`Mub6Maximum.ThreeBasis.bases` (computational / `H` / `K`
columns, the paper's T0 with `|j_z,J_z⟩`, `|j_x,J_x⟩`, `|j_y,J_y⟩`), no complex vector
`ψ ∈ C⁶` has all eighteen squared overlaps equal to `1/6` (Eq. (4)).  Its own development
explicitly disclaims T1 and the classification of all product triples.

Hence this paper-layer theorem is a faithful but **restricted** instance of Theorem 1
(canonical T0 only).  The T1 analysis (Eq. (5)) and the transport of the statement along
the `ProductEquiv`-classes of Lemma 1 are the remaining gaps; the general analytic route of
pp. 4–7 (Steps 1–3, Eqs. (6)–(28)) is not formalised here.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Theorem1NoExtension

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- **Theorem 1, canonical T0 instance** (arXiv:1203.6887v2, Theorem 1, p. 4, Eq. (4)).
No vector `ψ ∈ C⁶`, product or not, is mutually unbiased to all three bases of the
canonical direct-product triple T0 (the eighteen conditions `|⟨j_a,J_a|ψ⟩|² = 1/6`).

Restricted to T0; the T1 instance and the general classification transport are not
covered here.  Proof: exact reuse of the Frozen theorem
`CanonicalUnextendibilityRestricted.canonicalUnextendibilityRestricted`. -/
theorem theorem1_canonical_T0 (ψ : QState (Fin 6)) :
    ¬ (∀ (r : Fin 3) (j : Fin 6),
        Complex.normSq (Inner (bases r j) ψ) = (1 : ℝ) / 6) :=
  Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth.canonicalUnextendibilityRestricted
    ψ

end Qatlib.Papers.MUBProduct12.TripleClassify.Theorem1NoExtension
