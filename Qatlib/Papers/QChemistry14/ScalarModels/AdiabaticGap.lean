/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.AdiabaticGap

theorem gap_lower_bound_rpow (ε γ M : ℝ) (hε : 0 < ε) (hγ : 0 ≤ γ) (_hM : 0 < M) :
    ε ^ (-(Real.log M)) * γ ^ (Real.log M) = (γ / ε) ^ (Real.log M) := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  calc
    ε ^ (-(Real.log M)) * γ ^ (Real.log M)
        = (ε⁻¹) ^ (Real.log M) * γ ^ (Real.log M) := by
          rw [Real.rpow_neg_eq_inv_rpow]
    _ = (ε⁻¹ * γ) ^ (Real.log M) := by
          rw [← Real.mul_rpow (inv_nonneg.mpr hε0) hγ]
    _ = (γ / ε) ^ (Real.log M) := by
          rw [show ε⁻¹ * γ = γ / ε by rw [div_eq_inv_mul, mul_comm]]

theorem gap_lower_bound_mono (ε γ β M : ℝ) (hε : 0 < ε) (hγ : 0 ≤ γ)
    (_hβM : 0 ≤ β * M ^ (2 / 3 : ℝ)) (hγβ : γ ≤ β * M ^ (2 / 3 : ℝ))
    (_hM : 1 ≤ M) :
    ε ^ (-(Real.log M)) * γ ^ (Real.log M)
      ≤ ε ^ (-(Real.log M)) * (β * M ^ (2 / 3 : ℝ)) ^ (Real.log M) := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hε) _)
  exact Real.rpow_le_rpow hγ hγβ (Real.log_nonneg _hM)

theorem adiabatic_gap_lower_bound (ε γ β M : ℝ)
    (hε : 0 < ε) (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (_hM : 1 ≤ M)
    (hγβ : γ ≤ β * M ^ (2 / 3 : ℝ)) :
    ε ^ (-(Real.log M)) * γ ^ (Real.log M)
      ≤ ((β * M ^ (2 / 3 : ℝ)) / ε) ^ (Real.log M) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one _hM
  have _hβM : 0 ≤ β * M ^ (2 / 3 : ℝ) :=
    mul_nonneg hβ (Real.rpow_nonneg (le_of_lt hM0) _)
  calc
    ε ^ (-(Real.log M)) * γ ^ (Real.log M)
        ≤ ε ^ (-(Real.log M)) * (β * M ^ (2 / 3 : ℝ)) ^ (Real.log M) :=
          gap_lower_bound_mono ε γ β M hε hγ _hβM hγβ _hM
    _ = ((β * M ^ (2 / 3 : ℝ)) / ε) ^ (Real.log M) :=
          gap_lower_bound_rpow ε (β * M ^ (2 / 3 : ℝ)) M hε _hβM hM0

end Qatlib.Papers.QChemistry14.ScalarModels.AdiabaticGap
