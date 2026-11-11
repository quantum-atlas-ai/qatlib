/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults.Lemma5 — plat closure simulates randomized computation (c004)

Krovi--Russell, arXiv:1210.1550 (v2 PDF, §5, p.16–17, Lemma 5; extraction lines 642–646).

The source lemma is registered here as a `Prop`-valued contract of the abstract model
in `SourceModel`; this layer does not prove it.  The missing development is the
Ogburn–Preskill encoding of a dit as a strand pair closed in a plat, the reversible
circuit permutation matrix, the Johnson band construction of the group constants, and
the Lemma 6/Lemma 7 amplification argument.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- **Lemma 5** (arXiv:1210.1550, p.16–17, §5).  Given a randomized computation on `n`
bits and any `ε > 0`, there is a braid on `poly(n, 1/ε)` strands and `poly(n, 1/ε)`
crossings — with strands colored by the conjugacy-class fluxon irrep of the alternating
group `Aₘ`, `m ≥ 6`, with at least four fixed points — such that, writing `Pl` for the
plat closure of the braid and `Pₛ` for the success probability of the randomized
computation, `|Pₛ − Pl| < ε`.

The polynomial size is made explicit with the bound `(n + ⌈1/ε⌉ + 1)^6` on both the
number of strands `N` and of crossings `M`.  The group is `G = ↥(alternatingGroup
(Fin m))` and the color is the fluxon `Λ` (`Λ.chargeDim = 1`) whose representative
`Λ.flux.val` has at least four fixed points.

This is a statement registration, not a proof: the paper's encoding and amplification
machinery is not formalised in this layer.  The registered contract keeps the exact
quantitative form of the source so that a later development can target it unchanged. -/
def lemma5_plat_simulates_randomized
    (m : ℕ) (hm : 6 ≤ m)
    (I : ClosureInvariants ↥(alternatingGroup (Fin m)))
    (Λ : DGIrrep ↥(alternatingGroup (Fin m)))
    (hfluxon : Λ.chargeDim = 1)
    (hfix : FourFixedPoints Λ.flux.val)
    (n : ℕ) (R : RandomizedComputation n)
    {ε : ℝ} (hε : 0 < ε) :
    Prop :=
  ∃ (N M : ℕ) (b : BraidWord N M),
    N ≤ (n + invEps ε + 1) ^ 6 ∧
      M ≤ (n + invEps ε + 1) ^ 6 ∧
        ‖(R.successProbability : ℂ) - I.platClosure Λ b‖ < ε

end Qatlib.Papers.LinkInvQFT12.MainResults
