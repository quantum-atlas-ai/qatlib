/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

def MultiproductMassStructure : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℝ, (k : ℝ) < N →
    1 ≤ mCoeff k N (Fin.last k) ∧ ∃ q : Fin (k+1), mCoeff k N q < 0

end Qatlib.Papers.HamLCUSim12.Multiproduct
