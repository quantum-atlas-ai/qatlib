/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel
import Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp.Lemma20ScheduleC1C2

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral Gap Stability Across Four Discrete Adiabatic Time Steps

This module proves Lemma 21: under the discrete adiabatic evolution-time bound
`T ≥ 16 (√2)^p (κ^{p - 1} - 1) / (p - 1)`, the QLSP spectral gap schedule
`gap0 κ p` decreases by at most a constant factor `4 / 3` across any window
`s ≤ s' ≤ s + 4 / T`.

## Main statements

* `source_lemma21`: multiplicative stability `gap0 κ p s ≤ (4 / 3) * gap0 κ p s'`
  over four discrete time steps.

## References

* [Costa et al., 2022][CostaEtAl2022], Lemma 21, Eq. (H7), pp. 49--50.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

/-- **Lemma 21**: under `T ≥ 16 (√2)^p (κ^{p - 1} - 1) / (p - 1)`, for `1 < p`,
`1 < κ`, and `0 ≤ s ≤ s' ≤ s + 4 / T` with `s' ≤ 1`, the gap lower bound satisfies
`gap0 κ p s ≤ 4 / 3 * gap0 κ p s'`. -/
theorem source_lemma21
    (κ p T s s' : ℝ) (hp : 1 < p) (hκ : 1 < κ) (hT : 0 < T)
    (hs0 : 0 ≤ s) (_hs1 : s' ≤ 1) (hss : s ≤ s') (hs4 : s' ≤ s + 4 / T)
    (hTlarge : 16 * Real.sqrt 2 ^ p * ((κ ^ (p - 1) - 1) / (p - 1)) ≤ T) :
    gap0 κ p s ≤ 4 / 3 * gap0 κ p s' := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hκ0 : 0 < κ := lt_trans zero_lt_one hκ
  have hκ1 : κ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hκ)
  let B := κ ^ (p - 1) - 1
  have hB : 0 < B := sub_pos.mpr (Real.one_lt_rpow hκ hp1)
  let A := 1 + s * B
  let A' := 1 + s' * B
  have hA1 : 1 ≤ A := le_add_of_nonneg_right (mul_nonneg hs0 hB.le)
  have hA'1 : 1 ≤ A' :=
    le_add_of_nonneg_right (mul_nonneg (hs0.trans hss) hB.le)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA' : 0 < A' := lt_of_lt_of_le zero_lt_one hA'1
  have hgap (u : ℝ) : gap0 κ p u = (1 + u * B) ^ (1 / (1 - p)) := by
    dsimp [gap0, schedule, B]
    field_simp [ne_of_gt hκ0, hκ1]
    ring
  have hexponent : 1 / (1 - p) = -(1 / (p - 1)) := by
    rw [show 1 - p = -(p - 1) by ring, div_neg]
  have hsqrt : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hroot : 1 ≤ Real.sqrt 2 ^ p :=
    (Real.one_lt_rpow hsqrt (lt_trans zero_lt_one hp)).le
  have hquot : 0 < B / (p - 1) := div_pos hB hp1
  have hbase : 16 * (B / (p - 1)) ≤ T := by
    have hmul := mul_le_mul_of_nonneg_right hroot hquot.le
    change 16 * Real.sqrt 2 ^ p * (B / (p - 1)) ≤ T at hTlarge
    nlinarith
  have hBT : (4 / T) * B ≤ (p - 1) / 4 := by
    have hbound : 16 * B ≤ T * (p - 1) := by
      apply (div_le_iff₀ hp1).mp
      simpa only [mul_div_assoc] using hbase
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hT).2
    nlinarith
  have hratio : A' / A ≤ Real.exp ((p - 1) / 4) := by
    have hstep : 0 ≤ (s' - s) * B := mul_nonneg (sub_nonneg.mpr hss) hB.le
    calc
      A' / A = 1 + (s' - s) * B / A := by
        dsimp [A, A']
        field_simp [ne_of_gt hA]
        ring
      _ ≤ 1 + (s' - s) * B := by
        exact add_le_add_right (div_le_self hstep hA1) 1
      _ ≤ 1 + (4 / T) * B := by
        have hstep4 : s' - s ≤ 4 / T := by linarith
        exact add_le_add_right (mul_le_mul_of_nonneg_right hstep4 hB.le) 1
      _ ≤ 1 + (p - 1) / 4 := add_le_add_right hBT 1
      _ ≤ Real.exp ((p - 1) / 4) := by
        linarith [Real.add_one_le_exp ((p - 1) / 4)]
  have hexp : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have hneg : (3 / 4 : ℝ) ≤ Real.exp (-1 / 4 : ℝ) := by
      linarith [Real.add_one_le_exp (-1 / 4 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hneg (Real.exp_pos (1 / 4 : ℝ)).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    linarith
  have hpower : (A' / A) ^ (1 / (p - 1)) ≤ 4 / 3 := by
    calc
      (A' / A) ^ (1 / (p - 1)) ≤
          Real.exp ((p - 1) / 4) ^ (1 / (p - 1)) :=
        Real.rpow_le_rpow (div_nonneg hA'.le hA.le) hratio (by positivity)
      _ = Real.exp (1 / 4) := by
        rw [← Real.exp_mul]
        congr 1
        field_simp
      _ ≤ 4 / 3 := hexp
  rw [Real.div_rpow hA'.le hA.le] at hpower
  rw [hgap s, hgap s', hexponent]
  change A ^ (-(1 / (p - 1))) ≤ 4 / 3 * A' ^ (-(1 / (p - 1)))
  rw [Real.rpow_neg hA.le, Real.rpow_neg hA'.le]
  have hmain : (A ^ (1 / (p - 1)))⁻¹ ≤ (4 / 3) / A' ^ (1 / (p - 1)) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hA' _)).2
    simpa only [div_eq_mul_inv, mul_comm] using hpower
  simpa only [div_eq_mul_inv] using hmain

end Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp
