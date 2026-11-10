/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassBounds
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductKappaBoundStat
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

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
