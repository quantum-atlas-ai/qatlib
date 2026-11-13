/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassBounds
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductKappaBoundStat

/-!
# A lower scale for the multiproduct mass ratio

This module proves `multiproductKappaBound` by combining the first-k coefficient estimate with
positive and negative mass bounds. The conclusion is expressed without division: an explicit
nonnegative scale times the negative mass is bounded by the positive mass. See [ChildsWiebe2012]
for the multiproduct and linear-combination simulation framework.

## Main statements

* `multiproductKappaBound`: Under the analytic and terminal-node separation hypotheses, the
  negative coefficient mass times 2^(−1/2) k^(−5/2) exp(−2k(1 + log η / 2 − γ)) is at most the
  positive coefficient mass.
* `multiproduct_bound_scale`: For K > 0 and any real A, the product K(√2 K^(3/2)
  exp(2KA))(2^(−1/2) K^(−5/2) exp(−2KA)) equals 1.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

/-- For K > 0 and any real A, the product K(√2 K^(3/2) exp(2KA))(2^(−1/2) K^(−5/2) exp(−2KA))
equals 1. -/
theorem multiproduct_bound_scale (K A : ℝ) (hK : 0 < K) :
    K*(Real.sqrt 2*K^((3 : ℝ)/2)*Real.exp (2*K*A))*
      ((2 : ℝ)^(-(1 : ℝ)/2)*K^(-(5 : ℝ)/2)*Real.exp (-(2*K)*A)) = 1 := by
  have hp : 0 < K*(Real.sqrt 2*K^((3 : ℝ)/2)*Real.exp (2*K*A))*
      ((2 : ℝ)^(-(1 : ℝ)/2)*K^(-(5 : ℝ)/2)*Real.exp (-(2*K)*A)) := by positivity
  have hl : Real.log (K*(Real.sqrt 2*K^((3 : ℝ)/2)*Real.exp (2*K*A))*
      ((2 : ℝ)^(-(1 : ℝ)/2)*K^(-(5 : ℝ)/2)*Real.exp (-(2*K)*A))) = 0 := by
    repeat' rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.log_rpow hK,
      Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_rpow hK, Real.log_exp, Real.log_exp]
    ring
  rw [← Real.exp_log hp, hl, Real.exp_zero]

/-- Under the analytic and terminal-node separation hypotheses, the negative coefficient mass
times 2^(−1/2) k^(−5/2) exp(−2k(1 + log η / 2 − γ)) is at most the positive coefficient
mass. See [ChildsWiebe2012]. -/
theorem multiproductKappaBound : MultiproductKappaBound := by
  intro k hk γ η hγ hη hE hF hc
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN := multiproduct_exp_node_gt k hk γ hc
  let B := Real.sqrt 2*(k : ℝ)^((3 : ℝ)/2)*Real.exp (2*(k : ℝ)*(1+Real.log η/2-γ))
  let scale := (2 : ℝ)^(-(1 : ℝ)/2)*(k : ℝ)^(-(5 : ℝ)/2)*
    Real.exp (-(2*(k : ℝ))*(1+Real.log η/2-γ))
  apply multiproduct_kappa_of_coefficient_bound k hk _ hN B scale (by dsimp [scale]; positivity)
  · exact multiproductCoeffBound k hk γ η hγ hη hE hF hc
  · exact (multiproduct_bound_scale (k : ℝ) (1+Real.log η/2-γ) hkR).le

end Qatlib.Papers.HamLCUSim12.Multiproduct
