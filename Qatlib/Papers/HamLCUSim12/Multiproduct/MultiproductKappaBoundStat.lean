/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Multiproduct mass-ratio bound statement

The proposition `MultiproductKappaBound` specifies an explicit comparison between positive and
negative coefficient masses. It uses a multiplicative inequality to express the lower mass-ratio
scale supplied by the coefficient estimate, with the analytic and node-separation assumptions
stated explicitly. See [ChildsWiebe2012] for the multiproduct and linear-combination simulation
framework.

## Main statements

* `MultiproductKappaBound`: The proposition that, under the stated analytic and separation
  hypotheses, the negative coefficient mass multiplied by 2^(−1/2) k^(−5/2) exp(−2k(1 + log η /
  2 − γ)) is bounded by the positive mass.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition that, under the stated analytic and separation hypotheses, the negative
coefficient mass multiplied by 2^(−1/2) k^(−5/2) exp(−2k(1 + log η / 2 − γ)) is bounded by
the positive mass. -/
def MultiproductKappaBound : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ γ η : ℝ, 0 < γ → 1 / 4 < η →
    EtaMaxProperty η → FactorialLowerBound →
    2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
    (∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
        mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q < 0),
      |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q|)
      * ((2 : ℝ) ^ (-(1 : ℝ) / 2) * (k : ℝ) ^ (-(5 : ℝ) / 2)
          * Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ)))
      ≤ ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
        0 < mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q),
      mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q

end Qatlib.Papers.HamLCUSim12.Multiproduct
