/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordStat
set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

def MultiproductCoeffBoundCertified : Prop :=
  ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧
    ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ →
      2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
      ∀ q : Fin (k + 1), (q : ℕ) < k →
        |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤
          Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2) *
            Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ))

end Qatlib.Papers.HamLCUSim12.Multiproduct
