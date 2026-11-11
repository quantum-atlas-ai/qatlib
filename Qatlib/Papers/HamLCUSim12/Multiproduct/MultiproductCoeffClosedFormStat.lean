/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Multiproduct coefficient closed-form statement

The proposition `MultiproductCoeffClosedForm` specifies a factorial identity for coefficients at
the first k nodes. For positive N satisfying `NodesDistinct`, multiplying `mCoeff` by the
terminal squared-node difference and two factorials gives an explicit signed power of q + 1. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `MultiproductCoeffClosedForm`: The proposition equating the first-k coefficient times ((q +
  1)² − N²)(k + q + 1)!(k − q − 1)! with (−1)^(k − q − 1) 2(q + 1)^(2(k + 1)), assuming k ≥ 1, N
  > 0, and distinct nodes.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition equating the first-k coefficient times ((q + 1)² − N²)(k + q + 1)!(k − q −
1)! with (−1)^(k − q − 1) 2(q + 1)^(2(k + 1)), assuming k ≥ 1, N > 0, and distinct nodes. -/
def MultiproductCoeffClosedForm : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℝ, 0 < N → NodesDistinct k N →
    ∀ q : Fin (k+1), (q : ℕ) < k →
      mCoeff k N q * (((q : ℕ) + 1 : ℝ) ^ 2 - N ^ 2)
        * (((k + (q : ℕ) + 1).factorial : ℝ) * (((k : ℕ) - (q : ℕ) - 1).factorial : ℝ))
        = (-(1 : ℝ)) ^ ((k - (q : ℕ) - 1 : ℕ)) * 2 * (((q : ℕ) + 1 : ℝ) ^ (2 * (k + 1)))

end Qatlib.Papers.HamLCUSim12.Multiproduct
