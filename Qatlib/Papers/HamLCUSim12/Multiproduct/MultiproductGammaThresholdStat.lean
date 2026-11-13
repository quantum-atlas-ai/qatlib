/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Multiproduct exponent-threshold statement

The proposition `MultiproductGammaThreshold` encodes two consequences of an explicit lower bound
on γ: control of the negative coefficient mass by the positive mass and a bound on k² exp(−2γ(k
+ 1)). It retains `EtaMaxProperty` and `FactorialLowerBound` as hypotheses. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `MultiproductGammaThreshold`: The proposition that the stated γ threshold, with k ≥ 1, γ > 0,
  η > 1 / 4, 0 < δ ≤ 1, and the analytic inputs, implies four times the negative mass is at most
  δ times the positive mass and k² exp(−2γ(k + 1)) ≤ 1 / 2.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition that the stated γ threshold, with k ≥ 1, γ > 0, η > 1 / 4, 0 < δ ≤ 1, and
the analytic inputs, implies four times the negative mass is at most δ times the positive
mass and k² exp(−2γ(k + 1)) ≤ 1 / 2. -/
def MultiproductGammaThreshold : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ γ η δ : ℝ, 0 < γ → 1 / 4 < η → 0 < δ → δ ≤ 1 →
    EtaMaxProperty η → FactorialLowerBound →
    1 + Real.log η / 2 + (1 / (2 * (k : ℝ))) * Real.log ((2 * (k : ℝ)) ^ ((5 : ℝ) / 2) / δ) ≤ γ →
    (4 * ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
        mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q < 0),
        |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q|
      ≤ δ * ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) =>
        0 < mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q),
        mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q)
    ∧ (k : ℝ) ^ 2 * Real.exp (-(2 * γ) * ((k + 1 : ℕ) : ℝ)) ≤ 1 / 2

end Qatlib.Papers.HamLCUSim12.Multiproduct
