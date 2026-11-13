/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordStat

/-!
# Certified coefficient-bound statement

The proposition `MultiproductCoeffBoundCertified` asserts the existence of a single η in (0.305,
0.312) for the multiproduct coefficient estimate. Under the terminal-node separation condition,
every coefficient indexed below k is bounded by √2 k^(3/2) exp(2k(1 + log η / 2 − γ)). See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `MultiproductCoeffBoundCertified`: The proposition that some 0.305 < η < 0.312 bounds every
  first-k coefficient by √2 k^(3/2) exp(2k(1 + log η / 2 − γ)) whenever k ≥ 1, γ > 0, and 2k² ≤
  exp(2γ(k + 1)).

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The proposition that some 0.305 < η < 0.312 bounds every first-k coefficient by √2 k^(3/2)
exp(2k(1 + log η / 2 − γ)) whenever k ≥ 1, γ > 0, and 2k² ≤ exp(2γ(k + 1)). -/
def MultiproductCoeffBoundCertified : Prop :=
  ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧
    ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ →
      2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
      ∀ q : Fin (k + 1), (q : ℕ) < k →
        |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤
          Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2) *
            Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ))

end Qatlib.Papers.HamLCUSim12.Multiproduct
