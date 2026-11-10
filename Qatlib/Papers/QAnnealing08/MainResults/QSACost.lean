/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QAnnealing08.MainResults.QSACost

noncomputable def qsaComplexityBound (E_M γ d ε δ : ℝ) : ℝ :=
  (E_M / γ) ^ 2 * (Real.log (d / ε)) ^ 2 * Real.log d / (ε * Real.sqrt δ)

theorem qsa_complexity_bound
    (E_M γ d ε δ β_f Q N_QSA a b c : ℝ)
    (hE : 0 < E_M) (hγ : 0 < γ) (hd : 1 < d) (hε : 0 < ε) (hδ : 0 < δ)
    (hQ1 : 1 ≤ Q) (hQd : Q ≤ d)
    (hβ0 : 0 ≤ β_f)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN : N_QSA ≤ a * (Q * Real.log Q) / Real.sqrt δ)
    (hQ : Q ≤ b * β_f ^ 2 * E_M ^ 2 / ε)
    (hβ : β_f ≤ c * (Real.log (d / ε) / γ)) :
    N_QSA ≤ (a * b * c ^ 2) * qsaComplexityBound E_M γ d ε δ := by
  have hδpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hlogQ_le : Real.log Q ≤ Real.log d := Real.log_le_log hQpos hQd
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg (le_of_lt hd)

  have hB0 : 0 ≤ b * β_f ^ 2 * E_M ^ 2 / ε := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hb (sq_nonneg _)) (sq_nonneg _)
    · exact le_of_lt hε

  have hQlog : Q * Real.log Q ≤ (b * β_f ^ 2 * E_M ^ 2 / ε) * Real.log d :=
    mul_le_mul hQ hlogQ_le hlogQ0 hB0

  have hβsq : β_f ^ 2 ≤ c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2 := by
    have h1 := pow_le_pow_left₀ hβ0 hβ 2
    have heq : (c * (Real.log (d / ε) / γ)) ^ 2
        = c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2 := by ring
    rw [heq] at h1
    exact h1

  have hB_le : b * β_f ^ 2 * E_M ^ 2 / ε ≤
      b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2) * E_M ^ 2 / ε := by
    have hstep : b * β_f ^ 2 ≤ b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2) :=
      mul_le_mul_of_nonneg_left hβsq hb
    have hE2 : 0 ≤ E_M ^ 2 / ε := div_nonneg (sq_nonneg _) (le_of_lt hε)
    calc b * β_f ^ 2 * E_M ^ 2 / ε
        = (b * β_f ^ 2) * (E_M ^ 2 / ε) := by ring
      _ ≤ (b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2)) * (E_M ^ 2 / ε) :=
            mul_le_mul_of_nonneg_right hstep hE2
      _ = b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2) * E_M ^ 2 / ε := by ring

  have h1 : a * (Q * Real.log Q) / Real.sqrt δ
      ≤ a * ((b * β_f ^ 2 * E_M ^ 2 / ε) * Real.log d) / Real.sqrt δ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hδpos)
    exact mul_le_mul_of_nonneg_left hQlog ha
  have h2 : a * ((b * β_f ^ 2 * E_M ^ 2 / ε) * Real.log d) / Real.sqrt δ
      ≤ a * ((b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2) * E_M ^ 2 / ε)
          * Real.log d) / Real.sqrt δ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hδpos)
    apply mul_le_mul_of_nonneg_left _ ha
    exact mul_le_mul_of_nonneg_right hB_le hlogd0
  have hfinal :
      a * ((b * (c ^ 2 * (Real.log (d / ε)) ^ 2 / γ ^ 2) * E_M ^ 2 / ε)
          * Real.log d) / Real.sqrt δ
        = (a * b * c ^ 2) * qsaComplexityBound E_M γ d ε δ := by
    unfold qsaComplexityBound
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hδne : Real.sqrt δ ≠ 0 := ne_of_gt hδpos
    have hγne : γ ≠ 0 := ne_of_gt hγ
    field_simp
  exact hN.trans (h1.trans (h2.trans_eq hfinal))

theorem repeated_failure_bound (s : ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : 1 / ε ≤ (2 : ℝ) ^ s) :
    (1 / 2 : ℝ) ^ s ≤ ε := by
  rw [div_pow, one_pow]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  rw [div_le_iff₀ h2]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ s * ε := (div_le_iff₀ hε).mp h
  linarith [mul_comm ((2 : ℝ) ^ s) ε]

end Qatlib.Papers.QAnnealing08.MainResults.QSACost
