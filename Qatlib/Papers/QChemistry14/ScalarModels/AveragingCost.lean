/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.AveragingCost

noncomputable section

def sampleCount (C ε : ℝ) : ℝ := C ^ 2 / ε ^ 2

def measurementCount (Nint C ε : ℝ) : ℝ := Nint * C ^ 2 / ε ^ 2

theorem variance_le_precision (C ε N : ℝ) (_hε : 0 < ε) (hNpos : 0 < N)
    (hN : C ^ 2 / ε ^ 2 ≤ N) :
    C ^ 2 / N ≤ ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [div_le_iff₀ hε2] at hN
  rw [div_le_iff₀ hNpos]
  linarith

theorem sample_count_eq (C ε : ℝ) (hC : 0 < C) (_hε : 0 < ε) :
    C ^ 2 / sampleCount C ε = ε ^ 2 := by
  unfold sampleCount
  field_simp

theorem measurement_count_le (Nint C ε Ns : ℝ) (hNs : Ns ≤ sampleCount C ε)
    (hNint : 0 ≤ Nint) :
    Nint * Ns ≤ measurementCount Nint C ε := by
  unfold measurementCount sampleCount at *
  have hmul : Nint * Ns ≤ Nint * (C ^ 2 / ε ^ 2) :=
    mul_le_mul_of_nonneg_left hNs hNint
  calc
    Nint * Ns ≤ Nint * (C ^ 2 / ε ^ 2) := hmul
    _ = Nint * C ^ 2 / ε ^ 2 := by ring

theorem averaging_bigO (β h M ε : ℝ) (hM : 1 ≤ M) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (_hε : 0 < ε) :
    (M + M ^ 2) * (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ 2 / ε ^ 2
      ≤ (2 * (β + h) ^ 2) * M ^ 6 / ε ^ 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hpow : M ^ (5 / 3 : ℝ) ≤ M ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := M) (y := 5 / 3) (z := ((2:ℕ):ℝ)) hM
      (by norm_num)
    rwa [Real.rpow_natCast] at h
  have hM5 : 0 ≤ M ^ (5 / 3 : ℝ) := Real.rpow_nonneg (le_of_lt hMpos) _
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hB : β * M ^ (5 / 3 : ℝ) + h * M ^ 2 ≤ (β + h) * M ^ 2 := by
    have h1 : β * M ^ (5 / 3 : ℝ) ≤ β * M ^ 2 := mul_le_mul_of_nonneg_left hpow hβ
    have h2 : h * M ^ 2 ≤ h * M ^ 2 := le_rfl
    have hexp : (β + h) * M ^ 2 = β * M ^ 2 + h * M ^ 2 := by ring
    rw [hexp]
    linarith
  have hB0 : 0 ≤ β * M ^ (5 / 3 : ℝ) + h * M ^ 2 :=
    add_nonneg (mul_nonneg hβ hM5) (mul_nonneg hh hM2)
  have hsum : M + M ^ 2 ≤ 2 * M ^ 2 := by nlinarith
  have hB2 : (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ 2 ≤ ((β + h) * M ^ 2) ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  have hleft : (M + M ^ 2) * (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ 2
      ≤ (2 * M ^ 2) * ((β + h) * M ^ 2) ^ 2 :=
    mul_le_mul hsum hB2 (sq_nonneg _) (by nlinarith)
  have heq : (2 * M ^ 2) * ((β + h) * M ^ 2) ^ 2 = (2 * (β + h) ^ 2) * M ^ 6 := by
    ring
  calc
    (M + M ^ 2) * (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ 2 / ε ^ 2
        ≤ (2 * M ^ 2) * ((β + h) * M ^ 2) ^ 2 / ε ^ 2 :=
          div_le_div_of_nonneg_right hleft (sq_nonneg ε)
    _ = (2 * (β + h) ^ 2) * M ^ 6 / ε ^ 2 := by rw [heq]

end
end Qatlib.Papers.QChemistry14.ScalarModels.AveragingCost
