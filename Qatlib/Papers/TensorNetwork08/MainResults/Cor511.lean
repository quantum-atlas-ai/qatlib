/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Homogeneous Potts scale by coupling sign

Simplifies the homogeneous Potts scale expression in Corollary 5.11 of [AradLandau2010]. For
positive inverse temperature, the cycle-edge factor is `exp (β * J)` when `J > 0` and one
otherwise.

## Main statements

* `corollary5_11_potts_scale`: gives the two coupling-sign branches of the scale expression.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor511

/-- For positive `β`, the Potts scale with cycle factor `max (exp (β * J)) 1` equals the
exponential-factor expression when `J > 0` and the expression without that cycle factor
otherwise. See [AradLandau2010]. -/
theorem corollary5_11_potts_scale
    (q : ℕ) (β J : ℝ) (hβ : 0 < β) (nEtr nEcyc : ℕ) :
    (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ nEtr *
        (max (Real.exp (β * J)) 1) ^ nEcyc
      = if 0 < J then
          (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ nEtr *
            (Real.exp (β * J)) ^ nEcyc
        else
          (q : ℝ) * (Real.exp (β * J) + ((q : ℝ) - 1)) ^ nEtr := by
  by_cases hJ : 0 < J
  · rw [if_pos hJ]
    have h1 : (1 : ℝ) < Real.exp (β * J) := by
      have hpos : 0 < β * J := mul_pos hβ hJ
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp (β * J) := Real.exp_lt_exp.mpr hpos
    have hmax : max (Real.exp (β * J)) 1 = Real.exp (β * J) := by
      apply le_antisymm
      · exact max_le le_rfl (le_of_lt h1)
      · exact le_max_left _ _
    rw [hmax]
  · rw [if_neg hJ]
    have hle : Real.exp (β * J) ≤ 1 := by
      have hnonpos : β * J ≤ 0 := by
        have hJ' : J ≤ 0 := not_lt.mp hJ
        nlinarith [hβ, hJ']
      calc Real.exp (β * J) ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
        _ = 1 := Real.exp_zero
    have hmax : max (Real.exp (β * J)) 1 = 1 := by
      apply le_antisymm
      · exact max_le hle le_rfl
      · exact le_max_right _ _
    rw [hmax, one_pow, mul_one]

end Qatlib.Papers.TensorNetwork08.MainResults.Cor511
