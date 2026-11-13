/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Conditional multiproduct coefficient-bound statement

The proposition `MultiproductCoeffBound` specifies the first-k coefficient estimate under
`EtaMaxProperty` and `FactorialLowerBound`. It assumes k ≥ 1, γ > 0, η > 1/4, and sufficient
separation of the terminal exponential node. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `MultiproductCoeffBound`: The proposition bounding the first k coefficient magnitudes by √2
  k^(3/2) exp(2k(1 + log η / 2 − γ)) under the stated analytic and terminal-node separation
  hypotheses.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition bounding the first k coefficient magnitudes by √2 k^(3/2) exp(2k(1 + log η /
2 − γ)) under the stated analytic and terminal-node separation hypotheses. -/
def MultiproductCoeffBound : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ γ η : ℝ, 0 < γ → 1 / 4 < η →
    EtaMaxProperty η → FactorialLowerBound →
    2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
    ∀ q : Fin (k+1), (q : ℕ) < k →
      |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤
        Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2)
          * Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ))

end Qatlib.Papers.HamLCUSim12.Multiproduct
