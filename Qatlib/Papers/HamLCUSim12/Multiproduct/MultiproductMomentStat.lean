/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Multiproduct moment statement

The proposition `MultiproductMoment` states normalization and moment cancellation for `mCoeff`.
Its hypotheses require a positive terminal node satisfying `NodesDistinct`, ensuring the
interpolation nodes are nonzero and have distinct squares. See [ChildsWiebe2012] for the
multiproduct and linear-combination simulation framework.

## Main statements

* `MultiproductMoment`: The proposition that, for every positive terminal node satisfying
  `NodesDistinct`, the coefficients sum to 1 and the sums of `mCoeff k N q / mNode k N q ^ (2 *
  m)` vanish for 1 ≤ m ≤ k.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition that, for every positive terminal node satisfying `NodesDistinct`, the
coefficients sum to 1 and the sums of `mCoeff k N q / mNode k N q ^ (2 * m)` vanish for 1 ≤
m ≤ k. -/
def MultiproductMoment : Prop :=
  ∀ k : ℕ, ∀ N : ℝ, 0 < N → NodesDistinct k N →
    (∑ q : Fin (k+1), mCoeff k N q = 1) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      (∑ q : Fin (k+1), mCoeff k N q / mNode k N q ^ (2 * m)) = 0)

end Qatlib.Papers.HamLCUSim12.Multiproduct
