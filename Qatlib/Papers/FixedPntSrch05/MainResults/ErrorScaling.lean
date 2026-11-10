/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FixedPntSrch05.MainResults.ErrorScaling

def fixedPointError (ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | n + 1 => ε ^ 2 * fixedPointError ε n

theorem fixedPointError_eq_pow (ε : ℝ) (q : ℕ) :
    fixedPointError ε q = ε ^ (2 * q + 1) := by
  induction q with
  | zero => simp [fixedPointError]
  | succ n ih =>
      simp only [fixedPointError, ih, ← pow_add]
      congr 1
      omega

theorem fixedPointError_strictAntiOn {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    StrictAnti (fixedPointError ε) := by
  intro a b hab
  rw [fixedPointError_eq_pow, fixedPointError_eq_pow]

  have hsq : ε ^ 2 < 1 := by nlinarith
  have hpos : 0 < ε ^ (2 * a + 1) := pow_pos h0 _
  calc ε ^ (2 * b + 1) = ε ^ (2 * a + 1) * ε ^ (2 * (b - a)) := by
        rw [← pow_add]
        congr 1
        omega
    _ < ε ^ (2 * a + 1) * 1 := by
        exact mul_lt_mul_of_pos_left (pow_lt_one₀ h0.le h1 (by omega)) hpos
    _ = ε ^ (2 * a + 1) := by ring

theorem fixedPointError_le_classical (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (q : ℕ) :
    fixedPointError ε q ≤ ε ^ (q + 1) := by
  rw [fixedPointError_eq_pow]
  have hsplit : ε ^ (2 * q + 1) = ε ^ (q + 1) * ε ^ q := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  exact mul_le_of_le_one_right (pow_nonneg h0 _) (pow_le_one₀ h0 h1)

def swappedSuccess (ε : ℝ) : ℕ → ℝ
  | 0 => 1 - ε
  | n + 1 => (1 - ε) ^ 2 * swappedSuccess ε n

theorem swappedSuccess_eq_pow (ε : ℝ) (q : ℕ) :
    swappedSuccess ε q = (1 - ε) ^ (2 * q + 1) := by
  induction q with
  | zero => simp [swappedSuccess]
  | succ n ih =>
      simp only [swappedSuccess, ih, ← pow_add]
      congr 1
      omega

theorem swappedSuccess_at_one (q : ℕ) : swappedSuccess 1 q = 0 := by
  rw [swappedSuccess_eq_pow]
  simp

theorem error_le_exp_neg (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) (q : ℕ) :
    (1 - f) ^ (2 * q + 1) ≤ Real.exp (-((2 * (q : ℝ) + 1) * f)) := by
  have hbase : 0 ≤ 1 - f := by linarith
  have hle : 1 - f ≤ Real.exp (-f) := Real.one_sub_le_exp_neg f
  calc (1 - f) ^ (2 * q + 1) ≤ (Real.exp (-f)) ^ (2 * q + 1) :=
        pow_le_pow_left₀ hbase hle _
    _ = Real.exp (-((2 * (q : ℝ) + 1) * f)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem queries_sufficient (f δ : ℝ) (hf0 : 0 < f) (hf1 : f ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (q : ℕ)
    (hq : Real.log (1 / δ) ≤ (2 * (q : ℝ) + 1) * f) :
    fixedPointError (1 - f) q ≤ δ := by
  rw [fixedPointError_eq_pow]
  calc (1 - f) ^ (2 * q + 1)
      ≤ Real.exp (-((2 * (q : ℝ) + 1) * f)) := error_le_exp_neg f hf0.le hf1 q
    _ ≤ Real.exp (-Real.log (1 / δ)) := by
        apply Real.exp_le_exp.2
        linarith
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]

end Qatlib.Papers.FixedPntSrch05.MainResults.ErrorScaling
