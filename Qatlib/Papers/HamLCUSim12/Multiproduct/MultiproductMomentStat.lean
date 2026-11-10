/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

def MultiproductMoment : Prop :=
  ∀ k : ℕ, ∀ N : ℝ, 0 < N → NodesDistinct k N →
    (∑ q : Fin (k+1), mCoeff k N q = 1) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      (∑ q : Fin (k+1), mCoeff k N q / mNode k N q ^ (2 * m)) = 0)

end Qatlib.Papers.HamLCUSim12.Multiproduct
