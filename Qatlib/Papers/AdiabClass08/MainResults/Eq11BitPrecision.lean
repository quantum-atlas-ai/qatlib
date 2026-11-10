/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabClass08.MainResults

theorem lattice_root_step {N : ℕ} (hN : 0 < N) {bits X : ℝ} (hX : 0 ≤ X)
    (h : (2 : ℝ) ^ ((bits + 1) * (N : ℝ)) ≥ X ^ N) :
    (2 : ℝ) ^ (bits + 1) ≥ X := by

  have hrew : (2 : ℝ) ^ ((bits + 1) * (N : ℝ)) = ((2 : ℝ) ^ (bits + 1)) ^ N := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hpow : X ^ N ≤ ((2 : ℝ) ^ (bits + 1)) ^ N := by
    rw [← hrew]; exact h
  have hb : (0 : ℝ) ≤ (2 : ℝ) ^ (bits + 1) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  exact (pow_le_pow_iff_left₀ hX hb hN.ne').mp hpow

theorem eq11_bit_precision {S N : ℕ} (hS : 0 < S) (hN : 0 < N) {bits : ℝ}
    (h : (2 : ℝ) ^ (bits + 1) ≥ Real.exp 1 * ((S : ℝ) / (N : ℝ))) :
    bits ≥ Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1) - 1 := by
  have hb2 : (1 : ℝ) < 2 := by norm_num
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hfpos : (0 : ℝ) < (S : ℝ) / (N : ℝ) := by
    apply div_pos
    · exact_mod_cast hS
    · exact_mod_cast hN

  have hmul : Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1)
      = Real.logb 2 (((S : ℝ) / (N : ℝ)) * Real.exp 1) := by
    rw [Real.logb_mul (b := 2) hfpos.ne' hepos.ne']

  have hstep : Real.logb 2 (((S : ℝ) / (N : ℝ)) * Real.exp 1) ≤ bits + 1 := by
    rw [Real.logb_le_iff_le_rpow (b := 2) hb2 (by positivity)]
    calc ((S : ℝ) / (N : ℝ)) * Real.exp 1 = Real.exp 1 * ((S : ℝ) / (N : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (bits + 1) := h
  have : bits + 1 ≥ Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1) := by
    rw [hmul]; exact hstep
  linarith

theorem eq11_log_form {S N : ℕ} (hS : 0 < S) (hN : 0 < N) :
    Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1) - 1
      = Real.logb 2 (Real.exp 1 * ((S : ℝ) / (N : ℝ))) - 1 := by
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hfpos : (0 : ℝ) < (S : ℝ) / (N : ℝ) := by
    apply div_pos
    · exact_mod_cast hS
    · exact_mod_cast hN
  rw [Real.logb_mul (b := 2) hepos.ne' hfpos.ne']
  ring

theorem eq11_from_lattice_power {S N : ℕ} (hS : 0 < S) (hN : 0 < N) {bits : ℝ}
    (h : (2 : ℝ) ^ ((bits + 1) * (N : ℝ))
          ≥ (Real.exp 1 * (S : ℝ) / (N : ℝ)) ^ N) :
    bits ≥ Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1) - 1 := by
  have hX : (0 : ℝ) ≤ Real.exp 1 * (S : ℝ) / (N : ℝ) := by positivity
  have hroot : (2 : ℝ) ^ (bits + 1) ≥ Real.exp 1 * (S : ℝ) / (N : ℝ) :=
    lattice_root_step hN hX h

  have hroot' : (2 : ℝ) ^ (bits + 1) ≥ Real.exp 1 * ((S : ℝ) / (N : ℝ)) := by
    rw [mul_div_assoc] at hroot
    exact hroot
  exact eq11_bit_precision hS hN hroot'

end Qatlib.Papers.AdiabClass08.MainResults
