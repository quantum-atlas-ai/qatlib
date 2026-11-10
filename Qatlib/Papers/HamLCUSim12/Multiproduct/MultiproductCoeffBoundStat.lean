/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

def MultiproductCoeffBound : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ γ η : ℝ, 0 < γ → 1 / 4 < η →
    EtaMaxProperty η → FactorialLowerBound →
    2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
    ∀ q : Fin (k+1), (q : ℕ) < k →
      |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤
        Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2)
          * Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ))

end Qatlib.Papers.HamLCUSim12.Multiproduct
