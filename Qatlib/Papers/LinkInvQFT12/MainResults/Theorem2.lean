/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults.Theorem2 — quantum additive approximation (c001)

Krovi--Russell, arXiv:1210.1550 (v2 PDF, §4.2, p.14–15, Theorem 2; extraction line 582).

The source theorem is registered here as a `Prop`-valued contract of the abstract model
in `SourceModel`; this layer does not prove it.  The missing development is (i) a
formal R-matrix `τ_Λ(θ)` of `D(G)` and its unitary circuit, (ii) the Hadamard-test
estimator with its error analysis, and (iii) the Chernoff/union-bound sample count
`k > 32 log 2 / ε²`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- **Theorem 2** (arXiv:1210.1550, p.14–15, §4.2).  Given a braid `b ∈ Bₙ` of size `m`,
a finite group `G`, any irrep `([g], ρ)` of the quantum double `D(G)` and `ε > 0`, there
is a *quantum* algorithm that additively approximates both the trace and plat closures of
the braid, with strands colored by `([g], ρ)`, to additive error `ε`, in time
`O(poly(m, n, log|G|, 1/ε))`.

The `LinkAlgorithm` guarantee is uniform over all braids `b` (the algorithm receives `b`
as input), which is exactly the source's "given a braid `b ∈ Bₙ`" phrasing.

This is a statement registration, not a proof: the model records the output/error
contract and the polynomial cost ledger, while the QFT over `D(G)`, the R-matrix and the
sampling estimator are not formalised in this layer. -/
def theorem2_quantum_additive_approximation
    {G : Type*} [Group G] [Fintype G]
    (I : ClosureInvariants G) (Λ : DGIrrep G)
    {ε : ℝ} (hε : 0 < ε) :
    Prop :=
  ∃ A : LinkAlgorithm G I Λ ε,
    A.kind = AlgorithmKind.quantum ∧ PolyCost A.cost

end Qatlib.Papers.LinkInvQFT12.MainResults
