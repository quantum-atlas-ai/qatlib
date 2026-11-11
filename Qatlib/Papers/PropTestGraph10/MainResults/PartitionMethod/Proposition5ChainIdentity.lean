/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.Partition

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 5: the partition-lattice chain identity

Fixed source: arXiv:1012.3174v3 (20 Jun 2011), Proposition 5, p. 6.

For `L'' < L`, the sum of the chain coefficients `c_{L',L}` over the interval
`L'' ≤ L' ≤ L` vanishes.  This file states the proposition for the partition
lattice of `{1,…,k}` and proves it from the model development in
`Model.Partition`, where the general finite-poset identity is established
(`proposition5_chain_identity`): the recurrence `c(P,Q) = -∑_{P<R≤Q} c(R,Q)` is
satisfied by the paper's alternating chain count, and the recurrence implies
`∑_{P≤R≤Q} c(R,Q) = 1` if `P = Q` and `0` otherwise.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.PropTestGraph10.MainResults.PartitionMethod

open Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- Proposition 5 of the paper (p. 6).

Fixed source: arXiv:1012.3174v3, Proposition 5, p. 6.  Original statement:
"Suppose `L'' < L`. Then `∑_{L' : L'' ≤ L' ≤ L} c_{L',L} = 0`."

Proved from the recurrence definition of `chainCoeff` in `Model.Partition`
(eq. (12), p. 20): the recurrence gives
`∑_{L'' ≤ L' ≤ L} c_{L',L} = ∑_{L'' ≤ L' ≤ L} c_{L',L}` with the `L'' = L'`
term isolated, and the strict part telescopes to zero.  See
`Model.Partition.sum_chainCoeff_eq` and
`Model.Partition.proposition5_partition_identity`. -/
theorem proposition5_chain_identity {k : ℕ}
    {L'' L : Finpartition (Finset.univ : Finset (Fin k))} (h : L'' < L) :
    ∑ L' ∈ Finset.univ.filter
        (fun L' : Finpartition (Finset.univ : Finset (Fin k)) => L'' ≤ L' ∧ L' ≤ L),
        chainCoeff L' L = 0 :=
  proposition5_partition_identity h

end Qatlib.Papers.PropTestGraph10.MainResults.PartitionMethod
