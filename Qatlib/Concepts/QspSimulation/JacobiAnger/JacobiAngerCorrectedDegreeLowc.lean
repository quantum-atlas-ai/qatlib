/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeStat
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

section Helpers

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ≤ 3 := by linarith
  exact (Real.le_log_iff_exp_le (by norm_num)).mpr h3

private theorem div_pow_real (a b : ℝ) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  rw [div_eq_mul_inv, mul_pow, inv_pow, div_eq_mul_inv]

private theorem one_add_inv_pow_le_three (q : ℕ) (hq : 1 ≤ q) :
    (1 + 1 / (q : ℝ)) ^ q ≤ 3 := by
  have hsumpos : (0 : ℝ) < 1 + 1 / (q : ℝ) := by positivity
  have hle : Real.log (1 + 1 / (q : ℝ)) ≤ 1 / (q : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hsumpos
    linarith
  have hstep : (q : ℝ) * Real.log (1 + 1 / (q : ℝ)) ≤ (q : ℝ) * (1 / (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have hqone : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
    field_simp
  have hlog : Real.log ((1 + 1 / (q : ℝ)) ^ q) ≤ Real.log 3 := by
    rw [Real.log_pow]
    linarith [hstep, hqone, one_le_log_three]
  exact (Real.log_le_log_iff (by positivity) (by norm_num)).mp hlog

private theorem fact_ge_third_pow (q : ℕ) : ((q : ℝ) / 3) ^ q ≤ (q.factorial : ℝ) := by
  induction q with
  | zero => norm_num
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        norm_num
      · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        have h3 := one_add_inv_pow_le_three k hk1
        have hkey : ((k : ℝ) + 1) ^ k ≤ 3 * ((k : ℝ) ^ k) := by
          have hsplit : (1 + 1 / (k : ℝ)) ^ k
              = (((k : ℝ) + 1) ^ k) / ((k : ℝ) ^ k) := by
            rw [one_add_div (ne_of_gt hkpos), div_pow_real]
          rw [hsplit, div_le_iff₀ (pow_pos hkpos k)] at h3
          exact h3
        have hkk : ((k : ℝ) ^ k) = 3 ^ k * (((k : ℝ) / 3) ^ k) := by
          rw [div_pow_real]
          field_simp
        have hkm : ((k : ℝ) ^ k) ≤ 3 ^ k * ((k.factorial : ℝ)) := by
          rw [hkk]
          exact mul_le_mul_of_nonneg_left ih (by positivity)
        have h2 : ((k : ℝ) + 1) ^ (k + 1)
            ≤ ((k : ℝ) + 1) * (3 ^ k * ((k.factorial : ℝ))) * 3 := by
          have h1 : ((k : ℝ) + 1) ^ (k + 1)
              = ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ k) := by rw [pow_succ]; ring
          have h11 : ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ k)
              ≤ ((k : ℝ) + 1) * (3 * ((k : ℝ) ^ k)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
          have h12 : ((k : ℝ) + 1) * (3 * ((k : ℝ) ^ k))
              ≤ ((k : ℝ) + 1) * (3 ^ k * ((k.factorial : ℝ))) * 3 := by
            nlinarith [hkm, hkpos]
          nlinarith [h1, h11, h12]
        have hfinal2 : ((k : ℝ) + 1) * (3 ^ k * ((k.factorial : ℝ))) * 3
            = ((k : ℝ) + 1) * ((k.factorial : ℝ)) * 3 ^ (k + 1) := by
          rw [pow_succ]
          ring
        have h3le : ((3 : ℝ)) ≤ 3 ^ (k + 1) := by
          have h0 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
          rw [pow_succ]
          nlinarith [h0]
        have hden : (0 : ℝ) < 3 ^ (k + 1) := by positivity
        rw [Nat.factorial_succ]
        push_cast
        rw [div_pow_real, div_le_iff₀ hden]
        exact le_trans h2 (le_of_eq hfinal2)

private theorem cube_bound (u : ℝ) (hu : 0 ≤ u) :
    (1 + u) ^ ((1 : ℝ) / 3) * Real.log (1 + u) ≤ 2 * u := by
  have h1pos : (0 : ℝ) < 1 + u := by linarith
  have hvpos : (0 : ℝ) < (1 + u) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos h1pos ((1 : ℝ) / 3)
  have hv3 : ((1 + u) ^ ((1 : ℝ) / 3)) ^ 3 = 1 + u := by
    have hexp : ((1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 1 := by norm_num
    calc ((1 + u) ^ ((1 : ℝ) / 3)) ^ 3
        = ((1 + u) ^ ((1 : ℝ) / 3)) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
      _ = (1 + u) ^ (((1 : ℝ) / 3) * ((3 : ℕ) : ℝ)) :=
          (Real.rpow_mul h1pos.le ((1 : ℝ) / 3) ((3 : ℕ) : ℝ)).symm
      _ = (1 + u) ^ (1 : ℝ) := by rw [hexp]
      _ = 1 + u := Real.rpow_one _
  have hv1 : (1 : ℝ) ≤ (1 + u) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by linarith) (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
  have hlogv : Real.log ((1 + u) ^ ((1 : ℝ) / 3))
      ≤ (1 + u) ^ ((1 : ℝ) / 3) - 1 := Real.log_le_sub_one_of_pos hvpos
  have hquad : (0 : ℝ) < 2 * ((1 + u) ^ ((1 : ℝ) / 3))
      * ((1 + u) ^ ((1 : ℝ) / 3)) - (1 + u) ^ ((1 : ℝ) / 3) + 2 := by
    nlinarith [sq_nonneg (2 * (1 + u) ^ ((1 : ℝ) / 3) - 1)]
  have hfac : 2 * (((1 + u) ^ ((1 : ℝ) / 3)) ^ 3 - 1)
      - 3 * ((1 + u) ^ ((1 : ℝ) / 3) * (1 + u) ^ ((1 : ℝ) / 3)
        - (1 + u) ^ ((1 : ℝ) / 3))
      = ((1 + u) ^ ((1 : ℝ) / 3) - 1)
        * (2 * (1 + u) ^ ((1 : ℝ) / 3) * (1 + u) ^ ((1 : ℝ) / 3)
          - (1 + u) ^ ((1 : ℝ) / 3) + 2) := by
    ring
  have hge : 3 * ((1 + u) ^ ((1 : ℝ) / 3) * (1 + u) ^ ((1 : ℝ) / 3)
        - (1 + u) ^ ((1 : ℝ) / 3))
      ≤ 2 * (((1 + u) ^ ((1 : ℝ) / 3)) ^ 3 - 1) := by
    nlinarith [hfac, hv1, hquad]
  have hlogsplit : Real.log (1 + u)
      = 3 * Real.log ((1 + u) ^ ((1 : ℝ) / 3)) := by
    rw [← congrArg Real.log hv3, Real.log_pow]
    norm_num
  calc (1 + u) ^ ((1 : ℝ) / 3) * Real.log (1 + u)
      = (1 + u) ^ ((1 : ℝ) / 3) * (3 * Real.log ((1 + u) ^ ((1 : ℝ) / 3))) := by
        rw [← hlogsplit]
    _ ≤ (1 + u) ^ ((1 : ℝ) / 3)
        * (3 * ((1 + u) ^ ((1 : ℝ) / 3) - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hvpos.le
        exact mul_le_mul_of_nonneg_left hlogv (by norm_num)
    _ = 3 * ((1 + u) ^ ((1 : ℝ) / 3) * (1 + u) ^ ((1 : ℝ) / 3)
        - (1 + u) ^ ((1 : ℝ) / 3)) := by ring
    _ ≤ 2 * (((1 + u) ^ ((1 : ℝ) / 3)) ^ 3 - 1) := hge
    _ = 2 * u := by rw [hv3]; ring

end Helpers

theorem jacobiAngerCorrectedDegree : JacobiAngerCorrectedDegree := by
  intro τ ε hτ hεpos hεle
  refine ⟨?_, lcCorrectedQ_length_budget τ ε⟩
  have hq4 : 4 ≤ lcCorrectedQ τ ε := by
    unfold lcCorrectedQ
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  by_cases hτ0 : τ = 0
  · subst hτ0
    have hqR : ((lcCorrectedQ 0 ε : ℝ)) ≠ 0 := by
      have : (4 : ℝ) ≤ (lcCorrectedQ 0 ε : ℝ) := by exact_mod_cast hq4
      linarith
    rw [Real.zero_rpow hqR, mul_zero, zero_div]
    positivity
  · have hτpos : (0 : ℝ) < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
    set q : ℕ := lcCorrectedQ τ ε with hqdef
    have hLpos : (0 : ℝ) < Real.log (32 / ε) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hεpos]
      linarith
    have hm : (0 : ℝ) < max τ 1 := lt_of_lt_of_le (by norm_num) (le_max_right τ 1)
    have hupos : (0 : ℝ) < Real.log (32 / ε) / max τ 1 := div_pos hLpos hm
    have hlog1pos : (0 : ℝ) < Real.log (1 + Real.log (32 / ε) / max τ 1) := by
      refine Real.log_pos ?_
      linarith

    have hceil : 3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)
        ≤ (⌈3 * Real.log (32 / ε) /
            Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ) := Nat.le_ceil _
    have hbranch : (⌈3 * Real.log (32 / ε) /
          Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℕ) + 1 ≤ q := by
      rw [hqdef]
      unfold lcCorrectedQ
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hF3 : 3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)
        ≤ (q : ℝ) := by
      have h2 : ((⌈3 * Real.log (32 / ε) /
            Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) :=
        by exact_mod_cast hbranch
      linarith

    have hqlogu : 3 * Real.log (32 / ε)
        ≤ (q : ℝ) * Real.log (1 + Real.log (32 / ε) / max τ 1) :=
      (div_le_iff₀ hlog1pos).mp hF3
    have hτm : τ ≤ max τ 1 := le_max_left τ 1
    have hmuldiv : τ * (Real.log (32 / ε) / max τ 1)
        = (τ * Real.log (32 / ε)) / max τ 1 :=
      mul_div_assoc' τ (Real.log (32 / ε)) (max τ 1)
    have hdiv : τ * (Real.log (32 / ε) / max τ 1) ≤ Real.log (32 / ε) := by
      rw [hmuldiv, div_le_iff₀ hm]
      have h1 : τ * Real.log (32 / ε) ≤ max τ 1 * Real.log (32 / ε) :=
        mul_le_mul_of_nonneg_right hτm hLpos.le
      nlinarith [h1]
    have h2q : 2 * (Real.log (32 / ε) / max τ 1) / Real.log (1 + Real.log (32 / ε) / max τ 1)
        ≤ 2 * (q : ℝ) / (3 * τ) := by
      rw [div_le_div_iff₀ hlog1pos (by positivity : (0 : ℝ) < 3 * τ)]
      nlinarith [hqlogu, hdiv]
    have hkey := cube_bound (Real.log (32 / ε) / max τ 1) hupos.le
    have hbase : (1 + Real.log (32 / ε) / max τ 1) ^ ((1 : ℝ) / 3)
        ≤ 2 * (q : ℝ) / (3 * τ) := by
      refine le_trans ?_ h2q
      exact (le_div_iff₀ hlog1pos).mpr hkey
    have hlogq : Real.log (1 + Real.log (32 / ε) / max τ 1) / 3
        ≤ Real.log (2 * (q : ℝ) / (3 * τ)) := by
      have h1 : Real.log ((1 + Real.log (32 / ε) / max τ 1) ^ ((1 : ℝ) / 3))
          = Real.log (1 + Real.log (32 / ε) / max τ 1) / 3 := by
        rw [Real.log_rpow (by linarith) ((1 : ℝ) / 3)]
        field_simp
      have h2 : Real.log ((1 + Real.log (32 / ε) / max τ 1) ^ ((1 : ℝ) / 3))
          ≤ Real.log (2 * (q : ℝ) / (3 * τ)) :=
        Real.log_le_log (by positivity) hbase
      rw [h1] at h2
      exact h2
    have hfinal : Real.log (32 / ε) ≤ (q : ℝ) * Real.log (2 * (q : ℝ) / (3 * τ)) := by
      have h1 : (q : ℝ) * (Real.log (1 + Real.log (32 / ε) / max τ 1) / 3)
          ≤ (q : ℝ) * Real.log (2 * (q : ℝ) / (3 * τ)) :=
        mul_le_mul_of_nonneg_left hlogq (by positivity)
      nlinarith [h1, hqlogu]

    have hXpos : (0 : ℝ) < 2 * (q : ℝ) / (3 * τ) := by positivity
    have hbig : 32 / ε ≤ (2 * (q : ℝ) / (3 * τ)) ^ q := by
      calc 32 / ε = Real.exp (Real.log (32 / ε)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((q : ℝ) * Real.log (2 * (q : ℝ) / (3 * τ))) :=
            Real.exp_le_exp.mpr hfinal
        _ = (2 * (q : ℝ) / (3 * τ)) ^ q := by
            rw [← Real.log_pow, Real.exp_log (by positivity)]
    have hfact := fact_ge_third_pow q
    have hden : (0 : ℝ) < 2 ^ q * (q.factorial : ℝ) := by positivity
    have hden2 : (0 : ℝ) < 2 ^ q * (((q : ℝ) / 3) ^ q) := by positivity
    have hle1 : τ ^ q / (2 ^ q * (q.factorial : ℝ))
        ≤ τ ^ q / (2 ^ q * (((q : ℝ) / 3) ^ q)) := by
      rw [div_le_div_iff₀ hden hden2]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfact (by positivity)) (by positivity)
    have hEq : τ ^ q / (2 ^ q * (((q : ℝ) / 3) ^ q))
        = (3 * τ / (2 * (q : ℝ))) ^ q := by
      have hsplit : (3 * τ / (2 * (q : ℝ))) ^ q
          = 3 ^ q * τ ^ q / (2 ^ q * (q : ℝ) ^ q) := by
        rw [div_pow_real, mul_pow, mul_pow]
      rw [hsplit, div_pow_real]
      field_simp
    have hinv : (3 * τ / (2 * (q : ℝ))) ^ q
        = ((2 * (q : ℝ) / (3 * τ)) ^ q)⁻¹ := by
      have hd : (3 * τ / (2 * (q : ℝ))) = ((2 * (q : ℝ) / (3 * τ)))⁻¹ := by
        rw [inv_div]
      rw [hd, inv_pow]
    have hE2 : (32 : ℝ) ≤ ε * (2 * (q : ℝ) / (3 * τ)) ^ q := by
      have h9 := (div_le_iff₀ hεpos).mp hbig
      rw [mul_comm] at h9
      exact h9
    have hXqpos : (0 : ℝ) < (2 * (q : ℝ) / (3 * τ)) ^ q := pow_pos hXpos q
    have hfin2 : 4 * (((2 * (q : ℝ) / (3 * τ)) ^ q))⁻¹ ≤ ε / 8 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hXqpos]
      nlinarith [hE2]
    rw [Real.rpow_natCast τ q, Real.rpow_natCast 2 q]
    calc 4 * τ ^ q / (2 ^ q * (q.factorial : ℝ))
        = 4 * (τ ^ q / (2 ^ q * (q.factorial : ℝ))) := by ring
      _ ≤ 4 * (τ ^ q / (2 ^ q * (((q : ℝ) / 3) ^ q))) :=
          mul_le_mul_of_nonneg_left hle1 (by norm_num)
      _ = 4 * ((3 * τ / (2 * (q : ℝ))) ^ q) := by rw [hEq]
      _ = 4 * (((2 * (q : ℝ) / (3 * τ)) ^ q))⁻¹ := by rw [hinv]
      _ ≤ ε / 8 := hfin2

end Qatlib.Concepts.QspSimulation.JacobiAnger
