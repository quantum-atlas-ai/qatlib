/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

def MultiproductCoeffClosedForm : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℝ, 0 < N → NodesDistinct k N →
    ∀ q : Fin (k+1), (q : ℕ) < k →
      mCoeff k N q * (((q : ℕ) + 1 : ℝ) ^ 2 - N ^ 2)
        * (((k + (q : ℕ) + 1).factorial : ℝ) * (((k : ℕ) - (q : ℕ) - 1).factorial : ℝ))
        = (-(1 : ℝ)) ^ ((k - (q : ℕ) - 1 : ℕ)) * 2 * (((q : ℕ) + 1 : ℝ) ^ (2 * (k + 1)))

end Qatlib.Papers.HamLCUSim12.Multiproduct
