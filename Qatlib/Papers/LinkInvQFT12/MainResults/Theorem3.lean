/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults.Theorem3 — classical additive approximation for fluxons (c002)

Krovi--Russell, arXiv:1210.1550 (v2 PDF, §4.3, p.15, Theorem 3; extraction line 594).

The source theorem is registered here as a `Prop`-valued contract of the abstract model
in `SourceModel`; this layer does not prove it.  The missing development is the
permutation-matrix form of `τ_Λ(θ)` for a fluxon (eq. (4.6)) and the classical
Chernoff estimator with the same sample-count ledger as Theorem 2.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- **Theorem 3** (arXiv:1210.1550, p.15, §4.3).  Given a braid `b ∈ Bₙ` of size `m`, a
finite group `G` and any conjugacy class `[g]` of `G`, there is a *classical* algorithm
that additively approximates the trace and plat closures of the braid, with strands
colored by the fluxon irrep `([g], id)` of `D(G)`, to additive error `ε`, in time
`O(poly(m, n, log|G|, 1/ε))`.

The fluxon condition `([g], id)` — the trivial irrep `id` of the centralizer `Z(g)` — is
encoded by `Λ.chargeDim = 1` (a one-dimensional charge).  As for Theorem 2 the
`LinkAlgorithm` guarantee is uniform over all braids.

This is a statement registration, not a proof: the connection between the one-dimensional
charge field and the trivial centralizer irrep, the permutation action of eq. (4.6), and
the estimator analysis are not formalised in this layer. -/
def theorem3_classical_additive_approximation
    {G : Type*} [Group G] [Fintype G]
    (I : ClosureInvariants G) (Λ : DGIrrep G)
    (hfluxon : Λ.chargeDim = 1)
    {ε : ℝ} (hε : 0 < ε) :
    Prop :=
  ∃ A : LinkAlgorithm G I Λ ε,
    A.kind = AlgorithmKind.classical ∧ PolyCost A.cost

end Qatlib.Papers.LinkInvQFT12.MainResults
