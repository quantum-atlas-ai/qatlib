/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FixedPntSrch05.MainResults.GeneralAncilla

def generalError (ε r : ℝ) : ℕ → ℝ
  | 0 => ε
  | n + 1 => generalError ε r n * (1 - 2 * r * (1 - ε)) ^ 2

theorem generalError_eq_pow (ε r : ℝ) (q : ℕ) :
    generalError ε r q = ε * (1 - 2 * r * (1 - ε)) ^ (2 * q) := by
  induction q with
  | zero => simp [generalError]
  | succ n ih =>
      have hb : (1 - 2 * r * (1 - ε)) ^ (2 * (n + 1))
          = (1 - 2 * r * (1 - ε)) ^ (2 * n) * (1 - 2 * r * (1 - ε)) ^ 2 := by
        rw [← pow_add]
        congr 1
      simp only [generalError, ih]
      rw [hb]
      ring

theorem threshold_mem (r : ℝ) (hr0 : 1 / 2 < r) (hr1 : r ≤ 1) :
    0 < (2 * r - 1) / (2 * r + 1) ∧ (2 * r - 1) / (2 * r + 1) ≤ 1 / 3 := by
  have hden : 0 < 2 * r + 1 := by linarith
  constructor
  · apply div_pos <;> linarith
  · rw [div_le_iff₀ hden]
    linarith

theorem error_at_zero_threshold (r ε0 : ℝ) (hr0 : 1 / 2 < r)
    (hε0 : ε0 = 1 - 1 / (2 * r)) (q : ℕ) (hq : 1 ≤ q) :
    ε0 * (1 - 2 * r * (1 - ε0)) ^ (2 * q) = 0 := by
  have hrne : r ≠ 0 := by linarith
  have hbase : 1 - 2 * r * (1 - ε0) = 0 := by
    rw [hε0]
    field_simp
    ring
  rw [hbase]
  have hq' : 2 * q ≠ 0 := by omega
  rw [zero_pow hq', mul_zero]

theorem error_lt_pow_of_threshold (ε r : ℝ) (hr0 : 1 / 2 < r)
    (hεrl : (2 * r - 1) / (2 * r + 1) < ε) (hε0 : 0 < ε) (hε1 : ε < 1)
    (q : ℕ) (hq : 1 ≤ q) :
    ε * (1 - 2 * r * (1 - ε)) ^ (2 * q) < ε ^ (2 * q + 1) := by
  have hden : 0 < 2 * r + 1 := by linarith

  have hlt : 2 * r - 1 < ε * (2 * r + 1) := (div_lt_iff₀ hden).mp hεrl
  have hb_gt : -(ε) < 1 - 2 * r * (1 - ε) := by
    nlinarith [hlt]
  have hb_lt : 1 - 2 * r * (1 - ε) < ε := by
    have hpos : 0 < (1 - ε) * (2 * r - 1) := mul_pos (by linarith) (by linarith)
    nlinarith [hpos]
  have hbabs : |1 - 2 * r * (1 - ε)| < ε := abs_lt.mpr ⟨hb_gt, hb_lt⟩
  have hpowabs : (1 - 2 * r * (1 - ε)) ^ (2 * q)
      = |1 - 2 * r * (1 - ε)| ^ (2 * q) := by
    have h1 : (1 - 2 * r * (1 - ε)) ^ (2 * q)
        = ((1 - 2 * r * (1 - ε)) ^ 2) ^ q := (pow_mul _ 2 q)
    rw [h1, show (1 - 2 * r * (1 - ε)) ^ 2 = |1 - 2 * r * (1 - ε)| ^ 2 from
      (sq_abs _).symm]
    exact (pow_mul |1 - 2 * r * (1 - ε)| 2 q).symm
  have hq' : 2 * q ≠ 0 := by omega
  have hpowlt : |1 - 2 * r * (1 - ε)| ^ (2 * q) < ε ^ (2 * q) :=
    pow_lt_pow_left₀ hbabs (abs_nonneg _) hq'
  calc ε * (1 - 2 * r * (1 - ε)) ^ (2 * q)
      = ε * |1 - 2 * r * (1 - ε)| ^ (2 * q) := by rw [hpowabs]
    _ < ε * ε ^ (2 * q) := mul_lt_mul_of_pos_left hpowlt hε0
    _ = ε ^ (2 * q + 1) := by rw [pow_succ']

end Qatlib.Papers.FixedPntSrch05.MainResults.GeneralAncilla
