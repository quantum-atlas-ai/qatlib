/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Real.Basic

/-!
# Multiproduct nodes and coefficients

This module defines the multiproduct node family `mNode`, consisting of 1 through k followed by
a real terminal node N, and the product-form coefficients `mCoeff`. The predicate
`NodesDistinct` requires N to differ from each of the first k nodes. See [ChildsWiebe2012] for
the multiproduct and linear-combination simulation framework.

## Main statements

* `mNode`: The multiproduct node at index q: q + 1 for q < k, and N at the final index.
* `mCoeff`: The multiproduct coefficient at q, defined as the product of `mNode k N q ^ 2 /
  (mNode k N q ^ 2 - mNode k N j ^ 2)` over indices j different from q.
* `NodesDistinct`: The property that the terminal node N differs from each of the initial nodes
  1 through k.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The multiproduct node at index q: q + 1 for q < k, and N at the final index. -/
noncomputable def mNode (k : ℕ) (N : ℝ) (q : Fin (k+1)) : ℝ :=
  if (q : ℕ) < k then ((q : ℕ) + 1 : ℝ) else N

/-- The multiproduct coefficient at q, defined as the product of `mNode k N q ^ 2 / (mNode k N q
^ 2 - mNode k N j ^ 2)` over indices j different from q. -/
noncomputable def mCoeff (k : ℕ) (N : ℝ) (q : Fin (k+1)) : ℝ :=
  ∏ j : Fin (k+1), if j = q then 1 else mNode k N q ^ 2 / (mNode k N q ^ 2 - mNode k N j ^ 2)

/-- The property that the terminal node N differs from each of the initial nodes 1 through k. -/
def NodesDistinct (k : ℕ) (N : ℝ) : Prop :=
  ∀ j : Fin (k+1), (j : ℕ) < k → N ≠ ((j : ℕ) + 1 : ℝ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
