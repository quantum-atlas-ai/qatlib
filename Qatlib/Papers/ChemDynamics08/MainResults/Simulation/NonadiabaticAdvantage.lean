/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ChemDynamics08.MainResults.Resources

set_option autoImplicit false

namespace Qatlib.Papers.ChemDynamics08.MainResults.Simulation

open Qatlib.Papers.ChemDynamics08.MainResults.Resources

noncomputable def bornOppenheimerCost (K B : ℕ) (m : ℝ) : ℝ :=
  (K : ℝ) ^ (3 * B - 6) * (5 / 4 * m ^ 3 + 5 / 2 * m ^ 2)

noncomputable def nonadiabaticCost (B : ℕ) (m : ℝ) : ℝ :=
  1000 * pairCount B * coulombPairCost m

private theorem fifteen_pow_lower (B : ℕ) (hB : 5 ≤ B) :
    (17700 : ℝ) * (B : ℝ) ^ 2 ≤ (15 : ℝ) ^ (3 * B - 6) := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
      have hexp : 3 * (B + 1) - 6 = (3 * B - 6) + 3 := by omega
      rw [hexp, pow_add]
      have h15 : (15 : ℝ) ^ (3 : ℕ) = 3375 := by norm_num
      rw [h15, Nat.cast_add, Nat.cast_one]
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
      have hsq : ((B : ℝ) + 1) ^ 2 ≤ 3375 * (B : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((B : ℝ) - 1), hB1]
      calc
        (17700 : ℝ) * ((B : ℝ) + 1) ^ 2
            ≤ 17700 * (3375 * (B : ℝ) ^ 2) := by nlinarith [hsq]
        _ = 3375 * ((17700 : ℝ) * (B : ℝ) ^ 2) := by ring
        _ ≤ 3375 * (15 : ℝ) ^ (3 * B - 6) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (15 : ℝ) ^ (3 * B - 6) * 3375 := by ring

theorem nonadiabatic_dominates_born_oppenheimer
    (K B : ℕ) (m : ℝ) (hK : 15 ≤ K) (hB : 5 ≤ B) (hm : 1 ≤ m) :
    nonadiabaticCost B m < bornOppenheimerCost K B m := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  have hmpos : (0 : ℝ) < m := by linarith

  have hpow := fifteen_pow_lower B hB
  have hK15 : (15 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmono : (15 : ℝ) ^ (3 * B - 6) ≤ (K : ℝ) ^ (3 * B - 6) :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15) hK15 (3 * B - 6)
  have hboLower :
      22125 * (B : ℝ) ^ 2 * m ^ 3 + 44250 * (B : ℝ) ^ 2 * m ^ 2 ≤
        bornOppenheimerCost K B m := by
    unfold bornOppenheimerCost
    calc
      22125 * (B : ℝ) ^ 2 * m ^ 3 + 44250 * (B : ℝ) ^ 2 * m ^ 2
          = (17700 * (B : ℝ) ^ 2) * (5 / 4 * m ^ 3 + 5 / 2 * m ^ 2) := by ring
      _ ≤ (15 : ℝ) ^ (3 * B - 6) * (5 / 4 * m ^ 3 + 5 / 2 * m ^ 2) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ (K : ℝ) ^ (3 * B - 6) * (5 / 4 * m ^ 3 + 5 / 2 * m ^ 2) :=
            mul_le_mul_of_nonneg_right hmono (by positivity)

  have hna : nonadiabaticCost B m ≤ 22125 * (B : ℝ) ^ 2 * m ^ 3 := by
    have hc := coulomb_step_cost_cubic B m (by omega : 1 ≤ B) hm
    unfold nonadiabaticCost
    unfold coulombStepCost at hc
    nlinarith [hc]

  have hpos : (0 : ℝ) < 44250 * (B : ℝ) ^ 2 * m ^ 2 := by
    have h1 : (0 : ℝ) < (B : ℝ) ^ 2 := pow_pos hBpos 2
    have h2 : (0 : ℝ) < m ^ 2 := pow_pos hmpos 2
    positivity
  linarith

end Qatlib.Papers.ChemDynamics08.MainResults.Simulation
