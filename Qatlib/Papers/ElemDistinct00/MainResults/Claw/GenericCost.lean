/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.Claw

def clawSuccessProb (N M L : ℝ) : ℝ := L ^ 3 / (2 * N * M)

def clawRounds (N M L : ℝ) : ℝ := Real.sqrt (2 * N * M / L ^ 3)

def clawRoundCost (L : ℝ) : ℝ := L * Real.log L

def clawTotal (N M L : ℝ) : ℝ := clawRounds N M L * clawRoundCost L

def clawCost (N M L : ℝ) : ℝ := Real.sqrt (N * M / L) * Real.log L

theorem clawSuccessProb_arith {N M L : ℝ} (hN : 0 < N) (hM : 0 < M) :
    (L / N) * (L ^ 2 / M) * (1 / 2) = clawSuccessProb N M L := by
  unfold clawSuccessProb
  field_simp

theorem clawRounds_eq_inv_sqrt {N M L : ℝ} (hN : 0 < N) (hM : 0 < M) (hL : 0 < L) :
    clawRounds N M L = Real.sqrt (1 / clawSuccessProb N M L) := by
  unfold clawRounds clawSuccessProb
  congr 1
  field_simp

theorem sqrt_div_cube_mul {N M L : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    Real.sqrt (N * M / L ^ 3) * L = Real.sqrt (N * M / L) := by
  rcases eq_or_lt_of_le hL with rfl | hLpos
  · simp
  · have hx0 : (0 : ℝ) ≤ N * M / L ^ 3 :=
      div_nonneg (mul_nonneg hN hM) (pow_pos hLpos 3).le
    have hsq : Real.sqrt (L ^ 2) = L := Real.sqrt_sq hLpos.le
    calc Real.sqrt (N * M / L ^ 3) * L
        = Real.sqrt (N * M / L ^ 3) * Real.sqrt (L ^ 2) := by rw [hsq]
      _ = Real.sqrt ((N * M / L ^ 3) * L ^ 2) := by rw [Real.sqrt_mul hx0]
      _ = Real.sqrt (N * M / L) := by
          congr 1
          field_simp

theorem clawTotal_eq {N M L : ℝ} (hN : 0 < N) (hM : 0 < M) (hL : 0 < L) :
    clawTotal N M L = Real.sqrt 2 * clawCost N M L := by
  unfold clawTotal clawRounds clawRoundCost clawCost
  have hsplit : Real.sqrt (2 * N * M / L ^ 3)
      = Real.sqrt 2 * Real.sqrt (N * M / L ^ 3) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hstep := sqrt_div_cube_mul (le_of_lt hN) (le_of_lt hM) (le_of_lt hL)
  rw [hsplit]
  calc Real.sqrt 2 * Real.sqrt (N * M / L ^ 3) * (L * Real.log L)
      = Real.sqrt 2 * (Real.sqrt (N * M / L ^ 3) * L) * Real.log L := by ring
    _ = Real.sqrt 2 * (Real.sqrt (N * M / L) * Real.log L) := by rw [hstep]; ring

theorem sqrt_sqrt_eq_rpow_quarter {M : ℝ} (hM : 0 ≤ M) :
    Real.sqrt (Real.sqrt M) = M ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hM]
  congr 1
  norm_num

theorem clawCost_sqrtM_eq {N M : ℝ} (hN : 0 ≤ N) (hM : 0 < M) :
    clawCost N M (Real.sqrt M)
      = Real.sqrt N * M ^ (1 / 4 : ℝ) * Real.log (Real.sqrt M) := by
  unfold clawCost
  have hM0 : (0 : ℝ) ≤ M := le_of_lt hM
  have h1 : N * M / Real.sqrt M = N * Real.sqrt M := by
    rw [mul_div_assoc, Real.div_sqrt]
  rw [h1, Real.sqrt_mul hN, sqrt_sqrt_eq_rpow_quarter hM0]

theorem clawCost_sqrtM_le {N M : ℝ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : M ≤ N ^ 2) :
    clawCost N M (Real.sqrt M) ≤ Real.sqrt N * M ^ (1 / 4 : ℝ) * Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  rw [clawCost_sqrtM_eq hNpos.le hMpos]
  have hlog : Real.log (Real.sqrt M) ≤ Real.log N := by
    apply Real.log_le_log (Real.sqrt_pos_of_pos hMpos)
    exact (Real.sqrt_le_left hNpos.le).mpr hMN
  have hnonneg : (0 : ℝ) ≤ Real.sqrt N * M ^ (1 / 4 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hMpos.le _)
  exact mul_le_mul_of_nonneg_left hlog hnonneg

theorem clawCost_N_eq {N M : ℝ} (hN : 0 < N) (hM : 0 ≤ M) :
    clawCost N M N = Real.sqrt M * Real.log N := by
  unfold clawCost
  rw [show N * M / N = M by field_simp]

theorem min_eq_sqrtM {N M : ℝ} (hN : 1 ≤ N) (h : M ≤ N ^ 2) :
    min N (Real.sqrt M) = Real.sqrt M := by
  apply min_eq_right
  exact (Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ N)).mpr h

theorem min_eq_N {N M : ℝ} (hN : 1 ≤ N) (h : N ^ 2 < M) :
    min N (Real.sqrt M) = N := by
  apply min_eq_left
  rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ N)]
  exact Real.sqrt_le_sqrt h.le

theorem clawCost_min_bound {N M : ℝ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    clawCost N M (min N (Real.sqrt M))
      ≤ (if M ≤ N ^ 2 then Real.sqrt N * M ^ (1 / 4 : ℝ) * Real.log N
          else Real.sqrt M * Real.log N) := by
  by_cases h : M ≤ N ^ 2
  · rw [min_eq_sqrtM hN h, if_pos h]
    exact clawCost_sqrtM_le hN hM h
  · have hlt : N ^ 2 < M := lt_of_not_ge h
    rw [min_eq_N hN hlt, if_neg h, clawCost_N_eq (by linarith) (by linarith)]

end Qatlib.Papers.ElemDistinct00.MainResults.Claw
