/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Archimedean
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

def phasePrecisionBits (n : ℕ) (ε : ℝ) : ℕ :=
  n + Nat.ceil (Real.logb 2 (1 / (2 * ε) + 1 / 2))

def phasePrecisionBitsSucc (n : ℕ) (ε : ℝ) : ℕ :=
  n + 1 + Nat.ceil (Real.logb 2 (1 / ε))

theorem amplified_precision_corrected (n : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ω : ℝ) :
    1 - ε ≤
      bhmt11WindowMass (2 ^ phasePrecisionBitsSucc n ε) ω (1 / (2 : ℝ) ^ (n + 1)) := by
  let c : ℕ := Nat.ceil (Real.logb 2 (1 / ε))
  let K : ℝ := (2 : ℝ) ^ c
  have hεhalf_pos : (0 : ℝ) < 1 / ε := by positivity
  have hlog : 0 < Real.logb 2 (1 / ε) :=
    Real.logb_pos (by norm_num) (by
      rw [one_div]
      exact (one_lt_inv₀ hε0).mpr hε1)
  have hc : 0 < c := by
    simpa only [c] using Nat.ceil_pos.mpr hlog
  have hc1 : 1 ≤ c := hc
  have hK2 : (2 : ℝ) ≤ K := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ c := pow_le_pow_right₀ (by norm_num) hc1
    simpa [K] using h2
  have hKgt : 1 < K := by linarith
  have hMpos : 0 < 2 ^ phasePrecisionBitsSucc n ε := Nat.two_pow_pos _
  have hMcast : ((2 ^ phasePrecisionBitsSucc n ε : ℕ) : ℝ) = (2 : ℝ) ^ (n + 1) * K := by
    rw [show phasePrecisionBitsSucc n ε = n + 1 + c from rfl]
    push_cast
    rw [pow_add]
  have hKM : K / ((2 ^ phasePrecisionBitsSucc n ε : ℕ) : ℝ)
      = 1 / (2 : ℝ) ^ (n + 1) := by
    rw [hMcast]
    have ha : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
    have hb : (0 : ℝ) < K := by positivity
    field_simp
  have htail := bhmt_phase_estimation_theorem11_tail
    (2 ^ phasePrecisionBitsSucc n ε) ω hMpos K hKgt
  rw [hKM] at htail
  have hKge : 1 / ε ≤ K := by
    have hceil : Real.logb 2 (1 / ε) ≤ (c : ℝ) := by
      have h := (Nat.ceil_le (a := Real.logb 2 (1 / ε))
        (n := Nat.ceil (Real.logb 2 (1 / ε)))).mp (le_refl _)
      simpa only [c] using h
    have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hceil
    rw [Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hεhalf_pos] at h
    rwa [Real.rpow_natCast] at h
  have hfin : 1 / (2 * (K - 1)) ≤ ε := by
    have hpos : 0 < 2 * (K - 1) := by nlinarith
    rw [div_le_iff₀ hpos]
    by_cases hhalf : ε ≤ 1 / 2
    · have hεK : (1 : ℝ) ≤ ε * K := by
        have hm := mul_le_mul_of_nonneg_left hKge (le_of_lt hε0)
        have he : ε * (1 / ε) = 1 := by field_simp
        rwa [he] at hm
      nlinarith
    · push Not at hhalf
      nlinarith
  linarith

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
