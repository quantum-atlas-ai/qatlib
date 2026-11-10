/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.OptimizedBound.OptimizedAdversaryQueryLowerBoundStat
import Mathlib.Tactic.NormNum.RealSqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.ConversionCore.OptimizedBound
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal

theorem optimizedAdversaryQueryLowerBound : OptimizedAdversaryQueryLowerBound := by
  intro X W _ _ _ _ _ n input f C ψ E ε hC hψ he0 he1 hs
  have hprod : ε * (1 - ε) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (ε - 1 / 2)]
  have hsqrt := Real.sqrt_le_sqrt hprod
  norm_num at hsqrt
  have hc : 0 ≤ 1 - 2 * Real.sqrt (ε * (1 - ε)) := by linarith
  rw [generalAdversaryValue, ENNReal.mul_iSup]
  apply iSup_le
  intro Γ
  have hreal := negative_adversary_actual_bounded_error_circuit_lower_bound X W n input
    Γ.1 f C ψ E ε Γ.2.1 Γ.2.2.1 hC hψ he0 he1 hs
  have hb := generalAdversary_filter_bound input Γ.1 Γ.2.2.2
  have hcost : (1 - 2 * Real.sqrt (ε * (1 - ε))) * ‖Γ.1‖ ≤ 2 * (QueryCount C : ℝ) := by
    calc
      _ ≤ 2 * (QueryCount C : ℝ) * advFilterBound input Γ.1 := hreal
      _ ≤ 2 * (QueryCount C : ℝ) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := mul_one _
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal hcost

end Qatlib.Concepts.ConversionCore.OptimizedBound
