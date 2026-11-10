/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.QueryBound.CostDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.QueryBound

open scoped BigOperators

def kClawDetectCost (k : ℕ) (P L : ℝ) : ℝ :=
  szegedyCost ((k : ℝ) * L * Real.log ((k : ℝ) * L)) 0 (Real.log ((k : ℝ) * L))
    (1 / L) (L ^ k / P)

def kClawDetectStandardCost (k : ℕ) (P L : ℝ) : ℝ :=
  szegedyCost ((k : ℝ) * L) 0 1 (1 / L) (L ^ k / P)

theorem szegedyCost_pos_form {CU CF CW δ ε : ℝ} (_h : 0 < δ * ε) :
    szegedyCost CU CF CW δ ε = CU + (CF + CW) * Real.sqrt (1 / (δ * ε)) := by
  have h1 : (CF + CW) / Real.sqrt (δ * ε) = (CF + CW) * Real.sqrt (1 / (δ * ε)) := by
    rw [div_eq_mul_inv, one_div, ← Real.sqrt_inv]
  rw [szegedyCost, h1]

theorem pow_eq_pow_sub_mul {L : ℝ} {k : ℕ} (hk : 0 < k) : L ^ k = L ^ (k - 1) * L := by
  conv_lhs => rw [show k = (k - 1) + 1 by omega]
  rw [pow_succ]

theorem pow_succ_div_pow_sub {L : ℝ} {k : ℕ} (hL : L ≠ 0) (hk : 2 ≤ k) :
    L ^ (k + 1) / L ^ (k - 1) = L * L := by
  have hdiv : L ^ (k + 1) = L ^ (k - 1) * L ^ 2 := by
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
  rw [hdiv]
  field_simp

theorem pow_div_pow_sub {N : ℝ} {k : ℕ} (hN : N ≠ 0) (hk : 2 ≤ k) :
    N ^ k / N ^ (k - 2) = N * N := by
  have hdiv : N ^ k = N ^ (k - 2) * N ^ 2 := by
    conv_lhs => rw [show k = (k - 2) + 2 by omega]
    rw [pow_add]
  rw [hdiv]
  field_simp

theorem kClawDetectCost_eq {k : ℕ} (hk : 0 < k) {P L : ℝ} (hP : 0 < P) (hL : 0 < L) :
    kClawDetectCost k P L
      = (k : ℝ) * L * Real.log ((k : ℝ) * L)
        + Real.log ((k : ℝ) * L) * Real.sqrt (P / L ^ (k - 1)) := by
  have hδε : (1 / L) * (L ^ k / P) = L ^ (k - 1) / P := by
    rw [pow_eq_pow_sub_mul hk]
    field_simp
  have hpos : 0 < (1 / L) * (L ^ k / P) := by
    rw [hδε]
    positivity
  rw [kClawDetectCost, szegedyCost_pos_form hpos, hδε]
  have hsqrt : Real.sqrt (1 / (L ^ (k - 1) / P)) = Real.sqrt (P / L ^ (k - 1)) := by
    congr 1
    field_simp
  rw [hsqrt]
  ring

theorem kClawDetectStandardCost_eq {k : ℕ} (hk : 0 < k) {P L : ℝ} (hP : 0 < P)
    (hL : 0 < L) :
    kClawDetectStandardCost k P L
      = (k : ℝ) * L + Real.sqrt (P / L ^ (k - 1)) := by
  have hδε : (1 / L) * (L ^ k / P) = L ^ (k - 1) / P := by
    rw [pow_eq_pow_sub_mul hk]
    field_simp
  have hpos : 0 < (1 / L) * (L ^ k / P) := by
    rw [hδε]
    positivity
  rw [kClawDetectStandardCost, szegedyCost_pos_form hpos, hδε]
  have hsqrt : Real.sqrt (1 / (L ^ (k - 1) / P)) = Real.sqrt (P / L ^ (k - 1)) := by
    congr 1
    field_simp
  rw [hsqrt]
  ring

theorem rpow_inv_succ_pow (k : ℕ) (hk : 0 < k) {P : ℝ} (hP : 0 ≤ P) :
    (P ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = P := by
  have h := Real.rpow_mul hP (1 / ((k : ℝ) + 1)) (((k + 1 : ℕ)) : ℝ)
  rw [show (1 / ((k : ℝ) + 1)) * (((k + 1 : ℕ)) : ℝ) = 1 by
        push_cast
        field_simp, Real.rpow_one] at h
  rw [Real.rpow_natCast] at h
  exact h.symm

theorem mul_div_pow_sub {k : ℕ} (hk : 2 ≤ k) {N A : ℝ} (hN : N ≠ 0) :
    N * A / N ^ (k - 1) = A / N ^ (k - 2) := by
  rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  field_simp

theorem nat_le_two_pow : ∀ k : ℕ, k ≤ 2 ^ k
  | 0 => by simp
  | n + 1 => by
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      have ih := nat_le_two_pow n
      calc n + 1 ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

theorem log_mul_le {k : ℕ} (hk : 2 ≤ k) {L N1 : ℝ} (hL : 0 < L) (hLle : L ≤ N1)
    (hN1 : 2 ≤ N1) :
    Real.log ((k : ℝ) * L) ≤ ((k : ℝ) + 1) * Real.log N1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN10 : (0 : ℝ) < N1 := by linarith
  have harg0 : (0 : ℝ) < (k : ℝ) * L := mul_pos hkR hL
  have hkpow : (k : ℝ) ≤ N1 ^ k := by
    have h1 : (k : ℝ) ≤ 2 ^ k := by
      have h := nat_le_two_pow k
      exact_mod_cast h
    have h2 : (2 : ℝ) ^ k ≤ N1 ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
    linarith
  have hle : (k : ℝ) * L ≤ N1 ^ (k + 1) := by
    calc (k : ℝ) * L ≤ N1 ^ k * N1 :=
          mul_le_mul hkpow hLle (le_of_lt hL) (by positivity)
      _ = N1 ^ (k + 1) := by rw [pow_succ]
  have hlog := Real.log_le_log harg0 hle
  have hlogpow : Real.log (N1 ^ (k + 1)) = ((k : ℝ) + 1) * Real.log N1 := by
    rw [Real.log_pow]
    push_cast
    ring
  linarith

theorem kClawDetect_regime1_le {k : ℕ} (hk : 2 ≤ k) {P L N1 : ℝ} (hN1 : 2 ≤ N1)
    (hL : 0 < L) (hLle : L ≤ N1) (hP : P = L ^ (k + 1)) :
    kClawDetectCost k P L ≤ ((k : ℝ) + 1) ^ 2 * L * Real.log N1 := by
  have hk0 : 0 < k := by omega
  have hPpos : 0 < P := by rw [hP]; positivity
  rw [kClawDetectCost_eq hk0 hPpos hL, hP]
  have hsqrt : Real.sqrt (L ^ (k + 1) / L ^ (k - 1)) = L := by
    rw [pow_succ_div_pow_sub hL.ne' hk, show L * L = L ^ 2 by ring,
      Real.sqrt_sq (le_of_lt hL)]
  rw [hsqrt]
  have hlog := log_mul_le hk hL hLle hN1
  have hstep : ((k : ℝ) + 1) * L * Real.log ((k : ℝ) * L)
      ≤ ((k : ℝ) + 1) * L * (((k : ℝ) + 1) * Real.log N1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hfinal : ((k : ℝ) + 1) * L * (((k : ℝ) + 1) * Real.log N1)
      = ((k : ℝ) + 1) ^ 2 * L * Real.log N1 := by ring
  have hcost : (k : ℝ) * L * Real.log ((k : ℝ) * L)
      + Real.log ((k : ℝ) * L) * L
      = ((k : ℝ) + 1) * L * Real.log ((k : ℝ) * L) := by ring
  linarith [hcost]

theorem kClawDetect_regime2_le {k : ℕ} (hk : 2 ≤ k) {N1 A : ℝ} (hN1 : 2 ≤ N1)
    (hA : 0 < A) (hAk : N1 ^ k ≤ A) :
    kClawDetectCost k (N1 * A) N1
      ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 := by
  have hk0 : 0 < k := by omega
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hP : 0 < N1 * A := by positivity
  rw [kClawDetectCost_eq hk0 hP hN10, mul_div_pow_sub hk hN10.ne']
  have hNN : (0 : ℝ) < N1 ^ (k - 2) := by positivity
  have hsq_ge : N1 ^ 2 ≤ A / N1 ^ (k - 2) := by
    have h1 : N1 ^ k / N1 ^ (k - 2) = N1 ^ 2 := by
      rw [pow_div_pow_sub hN10.ne' hk, show N1 * N1 = N1 ^ 2 by ring]
    have h2 := div_le_div_of_nonneg_right hAk hNN.le
    rw [h1] at h2
    exact h2
  have hsqrt_ge : N1 ≤ Real.sqrt (A / N1 ^ (k - 2)) := by
    have h := Real.sqrt_le_sqrt hsq_ge
    rwa [Real.sqrt_sq (le_of_lt hN10)] at h
  have hlog := log_mul_le hk hN10 (le_refl N1) hN1
  have hlog0 : (0 : ℝ) ≤ Real.log ((k : ℝ) * N1) := by
    apply Real.log_nonneg
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hmul : (k : ℝ) * N1 ≤ (k : ℝ) * Real.sqrt (A / N1 ^ (k - 2)) :=
    mul_le_mul_of_nonneg_left hsqrt_ge hkR
  have hstep1 : (k : ℝ) * N1 * Real.log ((k : ℝ) * N1)
        + Real.log ((k : ℝ) * N1) * Real.sqrt (A / N1 ^ (k - 2))
      ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * Real.log ((k : ℝ) * N1) := by
    nlinarith [mul_le_mul_of_nonneg_right hmul hlog0]
  have hstep2 : ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * Real.log ((k : ℝ) * N1)
      ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2))
          * (((k : ℝ) + 1) * Real.log N1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hfinal : ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2))
        * (((k : ℝ) + 1) * Real.log N1)
      = ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 := by ring
  linarith

theorem kClawDetectStandard_regime1_le {k : ℕ} (hk : 2 ≤ k) {P L N1 : ℝ}
    (_hN1 : 2 ≤ N1) (hL : 0 < L) (_hLle : L ≤ N1) (hP : P = L ^ (k + 1)) :
    kClawDetectStandardCost k P L ≤ ((k : ℝ) + 1) * L := by
  have hk0 : 0 < k := by omega
  have hPpos : 0 < P := by rw [hP]; positivity
  rw [kClawDetectStandardCost_eq hk0 hPpos hL, hP]
  have hsqrt : Real.sqrt (L ^ (k + 1) / L ^ (k - 1)) = L := by
    rw [pow_succ_div_pow_sub hL.ne' hk, show L * L = L ^ 2 by ring,
      Real.sqrt_sq (le_of_lt hL)]
  rw [hsqrt]
  linarith

theorem kClawDetectStandard_regime2_le {k : ℕ} (hk : 2 ≤ k) {N1 A : ℝ}
    (hN1 : 2 ≤ N1) (hA : 0 < A) (hAk : N1 ^ k ≤ A) :
    kClawDetectStandardCost k (N1 * A) N1
      ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) := by
  have hk0 : 0 < k := by omega
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hP : 0 < N1 * A := by positivity
  rw [kClawDetectStandardCost_eq hk0 hP hN10, mul_div_pow_sub hk hN10.ne']
  have hNN : (0 : ℝ) < N1 ^ (k - 2) := by positivity
  have hsq_ge : N1 ^ 2 ≤ A / N1 ^ (k - 2) := by
    have h1 : N1 ^ k / N1 ^ (k - 2) = N1 ^ 2 := by
      rw [pow_div_pow_sub hN10.ne' hk, show N1 * N1 = N1 ^ 2 by ring]
    have h2 := div_le_div_of_nonneg_right hAk hNN.le
    rw [h1] at h2
    exact h2
  have hsqrt_ge : N1 ≤ Real.sqrt (A / N1 ^ (k - 2)) := by
    have h := Real.sqrt_le_sqrt hsq_ge
    rwa [Real.sqrt_sq (le_of_lt hN10)] at h
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hmul : (k : ℝ) * N1 ≤ (k : ℝ) * Real.sqrt (A / N1 ^ (k - 2)) :=
    mul_le_mul_of_nonneg_left hsqrt_ge hkR
  linarith

theorem lemma6_kClawDetect (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1)
    (hA : 0 < A) :
    (A ≤ N1 ^ k →
        kClawDetectCost k (N1 * A) ((N1 * A) ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1) ∧
    (N1 ^ k ≤ A →
        kClawDetectCost k (N1 * A) N1
          ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1) := by
  have hk0 : 0 < k := by omega
  have hN10 : (0 : ℝ) < N1 := by linarith
  constructor
  · intro hAle
    have hP : 0 < N1 * A := by positivity
    set L : ℝ := (N1 * A) ^ (1 / ((k : ℝ) + 1)) with hLdef
    have hcube : L ^ (k + 1) = N1 * A := rpow_inv_succ_pow k hk0 hP.le
    have hLpos : 0 < L := Real.rpow_pos_of_pos hP _
    have hle_pow : L ^ (k + 1) ≤ N1 ^ (k + 1) := by
      rw [hcube]
      calc N1 * A ≤ N1 * N1 ^ k := mul_le_mul_of_nonneg_left hAle hN10.le
        _ = N1 ^ (k + 1) := by rw [pow_succ]; ring
    have hLle : L ≤ N1 :=
      le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le hle_pow
    exact kClawDetect_regime1_le hk hN1 hLpos hLle hcube.symm
  · intro hAk
    exact kClawDetect_regime2_le hk hN1 hA hAk

theorem corollary7_kClawDetect (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1)
    (hA : 0 < A) :
    (A ≤ N1 ^ k →
        kClawDetectStandardCost k (N1 * A) ((N1 * A) ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1))) ∧
    (N1 ^ k ≤ A →
        kClawDetectStandardCost k (N1 * A) N1
          ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2))) := by
  have hk0 : 0 < k := by omega
  have hN10 : (0 : ℝ) < N1 := by linarith
  constructor
  · intro hAle
    have hP : 0 < N1 * A := by positivity
    set L : ℝ := (N1 * A) ^ (1 / ((k : ℝ) + 1)) with hLdef
    have hcube : L ^ (k + 1) = N1 * A := rpow_inv_succ_pow k hk0 hP.le
    have hLpos : 0 < L := Real.rpow_pos_of_pos hP _
    have hle_pow : L ^ (k + 1) ≤ N1 ^ (k + 1) := by
      rw [hcube]
      calc N1 * A ≤ N1 * N1 ^ k := mul_le_mul_of_nonneg_left hAle hN10.le
        _ = N1 ^ (k + 1) := by rw [pow_succ]; ring
    have hLle : L ≤ N1 :=
      le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le hle_pow
    exact kClawDetectStandard_regime1_le hk hN1 hLpos hLle hcube.symm
  · intro hAk
    exact kClawDetectStandard_regime2_le hk hN1 hA hAk

end Qatlib.Papers.ClawFinding07.MainResults.QueryBound
