/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AndersonLoc09.MainResults.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Real

theorem leadingSplitting_lambdaStar (N f2 : ℝ) (hN : 0 < N) (hf2 : 0 < f2) :
    leadingSplitting N (lambdaStar N f2) f2 = 4 := by
  unfold leadingSplitting lambdaStar
  have h2 : (Real.sqrt 2) ^ 4 = 4 := by
    rw [show (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num)]
    norm_num
  have hf4 : (Real.rpow f2 (-(1 / 4))) ^ 4 = f2⁻¹ := by
    rw [rpow_pow_nat f2 hf2 (-(1 / 4)) 4]
    rw [show (-(1 / 4 : ℝ) * ((4 : ℕ) : ℝ)) = -((1 : ℕ) : ℝ) by norm_num]
    rw [rpow_neg_fn f2 hf2 ((1 : ℕ) : ℝ), rpow_natcast_fn f2 1, pow_one]
  have hN4 : (Real.rpow N (-(1 / 8))) ^ 4 = Real.rpow N (-(1 / 2)) := by
    rw [rpow_pow_nat N hN (-(1 / 8)) 4]
    rw [show (-(1 / 8 : ℝ) * ((4 : ℕ) : ℝ)) = -(1 / 2 : ℝ) by norm_num]
  have hexp : (Real.sqrt 2 * Real.rpow f2 (-(1 / 4)) * Real.rpow N (-(1 / 8))) ^ 4
      = (Real.sqrt 2) ^ 4 * (Real.rpow f2 (-(1 / 4))) ^ 4
        * (Real.rpow N (-(1 / 8))) ^ 4 := by ring
  rw [hexp, h2, hf4, hN4]
  have hsN : Real.sqrt N * Real.rpow N (-(1 / 2)) = 1 := by
    have hsqrt : Real.sqrt N = Real.rpow N (1 / 2) := Real.sqrt_eq_rpow N
    rw [hsqrt, ← rpow_add_fn N hN (1 / 2) (-(1 / 2))]
    rw [show ((1 / 2 : ℝ) + -(1 / 2)) = 0 by norm_num, rpow_zero_fn N]
  rw [show Real.sqrt N * (4 * f2⁻¹ * Real.rpow N (-(1 / 2))) * f2
        = 4 * (Real.sqrt N * Real.rpow N (-(1 / 2))) * (f2⁻¹ * f2) by ring]
  rw [hsN, inv_mul_cancel₀ (ne_of_gt hf2)]
  ring

theorem splitting_ge_four_of_lambda_ge (N f2 lam : ℝ) (hN : 0 < N) (hf2 : 0 < f2)
    (hlam : lambdaStar N f2 ≤ lam) : 4 ≤ leadingSplitting N lam f2 := by
  have hstar_nonneg : 0 ≤ lambdaStar N f2 := by
    unfold lambdaStar
    exact le_of_lt (mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (Real.rpow_pos_of_pos hf2 _)) (Real.rpow_pos_of_pos hN _))
  have h4 := leadingSplitting_lambdaStar N f2 hN hf2
  unfold leadingSplitting at h4 ⊢
  have hpow : (lambdaStar N f2) ^ 4 ≤ lam ^ 4 := pow_le_pow_left₀ hstar_nonneg hlam 4
  have hcalc : Real.sqrt N * (lambdaStar N f2) ^ 4 * f2 ≤ Real.sqrt N * lam ^ 4 * f2 := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hf2)
    exact mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg N)
  linarith

theorem clause_anticrossing (E1 E2 shift : ℝ) (hgap : 4 ≤ E1 - E2) (hshift : shift < 4) :
    E2 + shift < E1 := by
  linarith

end Qatlib.Papers.AndersonLoc09.MainResults
