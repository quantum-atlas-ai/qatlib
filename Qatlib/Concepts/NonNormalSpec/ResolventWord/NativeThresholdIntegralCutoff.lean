/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

private theorem two_pow_clog_le_two_mul (n : ℕ) (hn : 0 < n) :
    2 ^ Nat.clog 2 n ≤ 2 * n := by
  by_cases hn1 : n = 1
  · subst n
    simp
  have hn2 : 1 < n := by omega
  have hk : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn2
  have hpred : 2 ^ (Nat.clog 2 n - 1) < n := by
    simpa only [Nat.pred_eq_sub_one] using!
      (Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hn2)
  have hpow : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
    conv_lhs => rw [show Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 from by omega]
    rw [pow_succ]
  rw [hpow]
  omega

theorem nativeAmplifierCutoff_bounds (γ δ ε : ℚ)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε) (_hε1 : ε ≤ 1 / 2) :
    let k := nativeAmplifierCutoff γ δ ε
    let B := nativeAmplifierLogBudget γ δ ε
    signPolynomialError (integratedThresholdGap (γ : ℝ) (δ : ℝ)) k ≤
        integratedThresholdTolerance (γ : ℝ) (δ : ℝ) (ε : ℝ) ∧
    (2 * 3 ^ k + 1 : ℝ) ≤
      1 + 8192 * (γ : ℝ) ^ 8 / (δ : ℝ) ^ 4 * (B : ℝ) ^ 2 ∧
    (B : ℝ) ≤ 2 +
      Real.log (1 / integratedThresholdTolerance (γ : ℝ) (δ : ℝ) (ε : ℝ)) /
        Real.log 2 := by
  let g := integratedThresholdGap (γ : ℝ) (δ : ℝ)
  let t := integratedThresholdTolerance (γ : ℝ) (δ : ℝ) (ε : ℝ)
  let gq := nativeAmplifierGap γ δ
  let tq := nativeAmplifierTolerance γ δ ε
  let C := Nat.ceil (1 / tq)
  let B := nativeAmplifierLogBudget γ δ ε
  let A := g⁻¹ ^ 2 * (B : ℝ)
  let Aq := gq⁻¹ ^ 2 * (B : ℚ)
  let Q := nativeAmplifierExponentBudget γ δ ε
  let k := nativeAmplifierCutoff γ δ ε
  let L := Real.log (1 / t)
  have hγr : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδr1 : (δ : ℝ) ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hδ1
    norm_num at hh
    exact hh
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hγpos : (0 : ℝ) < γ := by linarith
  have hgcast : (gq : ℝ) = g := by
    simp [gq, g, nativeAmplifierGap, integratedThresholdGap]
  have htcast : (tq : ℝ) = t := by
    simp [tq, t, nativeAmplifierTolerance, integratedThresholdTolerance, Rat.cast_min]
  have hAcast : (Aq : ℝ) = A := by
    simp [Aq, A, hgcast]
  have hgpos : 0 < g := by
    dsimp [g, integratedThresholdGap]
    positivity
  have hg8 : g ≤ 1 / 8 := by
    dsimp [g, integratedThresholdGap]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (γ : ℝ) ^ 2)).mpr
    nlinarith
  have htpos : 0 < t := by
    dsimp [t, integratedThresholdTolerance]
    positivity
  have htδ : t ≤ (δ : ℝ) / (4 * (γ : ℝ)) := min_le_right _ _
  have ht8 : t ≤ 1 / 8 := by
    refine htδ.trans ?_
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (γ : ℝ))).mpr
    nlinarith
  have h1t : (8 : ℝ) ≤ 1 / t := by
    apply (le_div_iff₀ htpos).mpr
    linarith
  have htqpos : 0 < tq := by
    have hh : (0 : ℝ) < (tq : ℝ) := by rwa [htcast]
    exact_mod_cast hh
  have h1tq : (8 : ℚ) ≤ 1 / tq := by
    have hh : (8 : ℝ) ≤ ((1 / tq : ℚ) : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_one, htcast] using! h1t
    exact_mod_cast hh
  have hClower : 1 / tq ≤ (C : ℚ) := Nat.le_ceil _
  have hC8 : 8 ≤ C := by exact_mod_cast (h1tq.trans hClower)
  have hBpos : 0 < B := Nat.clog_pos (by norm_num) (by omega : 1 < C)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (Nat.succ_le_of_lt hBpos)
  have hCpow : C ≤ 2 ^ B := Nat.le_pow_clog (by norm_num) C
  have h1tpow : 1 / t ≤ (2 : ℝ) ^ B := by
    have hq : 1 / tq ≤ ((2 ^ B : ℕ) : ℚ) :=
      hClower.trans (by exact_mod_cast hCpow)
    have hr : ((1 / tq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast hq
    simpa only [Rat.cast_div, Rat.cast_one, htcast] using! hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    convert! Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hLle : L ≤ (B : ℝ) := by
    have hh : L ≤ (B : ℝ) * Real.log 2 := by
      calc
        L ≤ Real.log ((2 : ℝ) ^ B) :=
          Real.log_le_log (by positivity : (0 : ℝ) < 1 / t) h1tpow
        _ = (B : ℝ) * Real.log 2 := Real.log_pow _ _
    exact hh.trans (by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left hlog2le (Nat.cast_nonneg B : (0 : ℝ) ≤ B))
  have hginv : 1 ≤ g⁻¹ := (one_le_inv₀ hgpos).mpr (by linarith)
  have hA1 : 1 ≤ A := by
    have hinv2 : 1 ≤ g⁻¹ ^ 2 := by nlinarith
    simpa only [one_mul, A] using!
      mul_le_mul hinv2 hB1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hAq1 : (1 : ℚ) ≤ Aq := by
    have hh : (1 : ℝ) ≤ (Aq : ℝ) := by rwa [hAcast]
    exact_mod_cast hh
  have hQlowerq : Aq ≤ (Q : ℚ) := Nat.le_ceil _
  have hQlower : A ≤ (Q : ℝ) := by
    have hh : (Aq : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQlowerq
    rwa [hAcast] at hh
  have hQpos : 0 < Q := by
    have hh : (0 : ℚ) < (Q : ℚ) := by linarith
    exact_mod_cast hh
  have hQupperq : (Q : ℚ) ≤ 2 * Aq := by
    have hh : (Q : ℚ) < Aq + 1 := Nat.ceil_lt_add_one (by linarith : (0 : ℚ) ≤ Aq)
    linarith
  have hQupper : (Q : ℝ) ≤ 2 * A := by
    have hh : (Q : ℝ) ≤ 2 * (Aq : ℝ) := by exact_mod_cast hQupperq
    rwa [hAcast] at hh
  have h2lower : A ≤ (2 : ℝ) ^ k := by
    have hh : (Q : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast (Nat.le_pow_clog (by norm_num : 1 < 2) Q)
    exact hQlower.trans hh
  have h2upper : (2 : ℝ) ^ k ≤ 4 * A := by
    have hh : (2 : ℝ) ^ k ≤ 2 * (Q : ℝ) := by
      exact_mod_cast (two_pow_clog_le_two_mul Q hQpos)
    linarith
  have hgA : g ^ 2 * A = (B : ℝ) := by
    dsimp [A]
    field_simp [hgpos.ne']
  have hbase : 1 - g ^ 2 ≤ Real.exp (-(g ^ 2)) := by
    have hh := Real.add_one_le_exp (-(g ^ 2))
    linarith
  have hbase0 : 0 ≤ 1 - g ^ 2 := by nlinarith
  have herr : signPolynomialError g k ≤ t := by
    unfold signPolynomialError
    calc
      (1 - g ^ 2) ^ (2 ^ k) ≤ (Real.exp (-(g ^ 2))) ^ (2 ^ k) :=
        pow_le_pow_left₀ hbase0 hbase _
      _ = Real.exp (((2 ^ k : ℕ) : ℝ) * (-(g ^ 2))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left h2lower (sq_nonneg g)
        rw [hgA] at hh
        push_cast
        nlinarith)
      _ = t := by
        rw [Real.exp_neg]
        dsimp [L]
        rw [Real.exp_log (by positivity : (0 : ℝ) < 1 / t)]
        simp
  have h3 : (3 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 2 := by
    calc
      (3 : ℝ) ^ k ≤ (4 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2 : ℝ) ^ k) ^ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have h3A : (3 : ℝ) ^ k ≤ 16 * A ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      (by positivity : (0 : ℝ) ≤ 4 * A)).mpr h2upper
    nlinarith
  have hginvdef : g⁻¹ = 4 * (γ : ℝ) ^ 2 / (δ : ℝ) := by
    dsimp [g, integratedThresholdGap]
    field_simp [hγpos.ne', hδr.ne']
  have hbudgeteq : 32 * A ^ 2 =
      8192 * (γ : ℝ) ^ 8 / (δ : ℝ) ^ 4 * (B : ℝ) ^ 2 := by
    dsimp [A]
    rw [hginvdef]
    field_simp [hδr.ne']
    ring
  have hCupperq : (C : ℚ) ≤ 2 / tq := by
    have hh : (C : ℚ) < 1 / tq + 1 :=
      Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ 1 / tq)
    have hq : (C : ℚ) ≤ 2 * (1 / tq) := by linarith
    rw [show (2 : ℚ) * (1 / tq) = 2 / tq by ring] at hq
    exact hq
  have hCupper : (C : ℝ) ≤ 2 / t := by
    have hh : (C : ℝ) ≤ ((2 / tq : ℚ) : ℝ) := by exact_mod_cast hCupperq
    simpa only [Rat.cast_div, Rat.cast_ofNat, htcast] using! hh
  have hBpred : (2 : ℝ) ^ (B - 1) < (C : ℝ) := by
    have hh : 2 ^ (B - 1) < C := by
      simpa only [Nat.pred_eq_sub_one] using!
        (Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < C))
    exact_mod_cast hh
  have hBlog : ((B : ℝ) - 1) * Real.log 2 ≤ Real.log 2 + L := by
    have hcast : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ B)]
      norm_num
    calc
      ((B : ℝ) - 1) * Real.log 2 = Real.log ((2 : ℝ) ^ (B - 1)) := by
        rw [Real.log_pow, hcast]
      _ ≤ Real.log (2 / t) := Real.log_le_log (by positivity) (hBpred.le.trans hCupper)
      _ = Real.log 2 + L := by
        rw [show (2 : ℝ) / t = 2 * (1 / t) by ring,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 1 / t ≠ 0)]
  have hBupper : (B : ℝ) ≤ 2 + L / Real.log 2 := by
    have he : 2 + L / Real.log 2 = (2 * Real.log 2 + L) / Real.log 2 := by
      field_simp
    rw [he]
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  refine ⟨herr, ?_, hBupper⟩
  change 2 * (3 : ℝ) ^ k + 1 ≤
    1 + 8192 * (γ : ℝ) ^ 8 / (δ : ℝ) ^ 4 * (B : ℝ) ^ 2
  rw [← hbudgeteq]
  linarith

end Qatlib.Concepts.NonNormalSpec.ResolventWord
