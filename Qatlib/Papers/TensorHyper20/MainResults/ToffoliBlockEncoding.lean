/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.TensorHyper20.MainResults.Definitions

/-!
# Explicit Toffoli bounds for tensor hypercontraction

Develops ceiling-division, square-root, and ceiling-logarithm estimates for the QROM blocking
choices in the tensor hypercontraction resource model of [LeeEtAl2021]. The scale `Lstar N`
controls the logarithmic register parameters.

Under the stated size and precision bounds, `exists_step_cost_polylog` chooses positive blocking
parameters with nonnegative step cost bounded by `200 * (N + 1) * (Lstar N)^3`. The main theorem
combines this estimate with phase-estimation iteration bounds.

## Main statements

* `qrom_balanced`: constructs a positive blocking parameter with an explicit square-root cost
  bound.
* `exists_step_cost_polylog`: provides positive parameters satisfying the step-cost bound.
* `main_result_total_toffoli`: bounds total Toffoli cost using the same resource hypotheses.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.ToffoliBlockEncoding

open Qatlib.Papers.TensorHyper20.MainResults

/-- For a positive divisor `k`, the natural ceiling-division expression is at most the natural
quotient `d / k` plus one. -/
theorem ceilDiv_le_div_add_one (d k : ℕ) (hk : 1 ≤ k) :
    ceilDiv d k ≤ d / k + 1 := by
  unfold ceilDiv
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hle : d + k - 1 ≤ d + k := by omega
  calc (d + k - 1) / k ≤ (d + k) / k := by gcongr
    _ = d / k + 1 := by rw [Nat.add_div_right _ hk0]

/-- For positive `k`, the real cast of `ceilDiv d k` is at most the real quotient `d / k` plus
one. -/
theorem ceilDiv_cast_le (d k : ℕ) (hk : 1 ≤ k) :
    (ceilDiv d k : ℝ) ≤ (d : ℝ) / (k : ℝ) + 1 := by
  calc (ceilDiv d k : ℝ) ≤ ((d / k + 1 : ℕ) : ℝ) := by
        exact_mod_cast ceilDiv_le_div_add_one d k hk
    _ = ((d / k : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (d : ℝ) / (k : ℝ) + 1 := by
        have h := Nat.cast_div_le (α := ℝ) (m := d) (n := k)
        linarith

/-- For a real number at least one, its square root is at most the number itself. -/
theorem sqrt_le_self {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith [sq_nonneg (x - 1)]⟩

/-- For positive natural numbers `d` and `m`, the real quotient `d / √(d / m)` equals `√(d *
m)`. -/
theorem sqrt_div_self (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    (d : ℝ) / Real.sqrt ((d : ℝ) / (m : ℝ)) = Real.sqrt ((d : ℝ) * (m : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hdm0 : (0 : ℝ) ≤ (d : ℝ) * (m : ℝ) := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt ((d : ℝ) / (m : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [div_eq_iff hs0.ne']
  rw [← Real.sqrt_mul hdm0]
  have harg : (d : ℝ) * (m : ℝ) * ((d : ℝ) / (m : ℝ)) = (d : ℝ) ^ 2 := by
    field_simp
  rw [harg, Real.sqrt_sq (le_of_lt hd0)]

/-- For positive natural `m`, the real product `m * √(d / m)` equals `√(d * m)`. -/
theorem m_mul_sqrt_div (d m : ℕ) (hm : 0 < m) :
    (m : ℝ) * Real.sqrt ((d : ℝ) / (m : ℝ)) = Real.sqrt ((d : ℝ) * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : Real.sqrt ((m : ℝ) ^ 2) = (m : ℝ) := Real.sqrt_sq hm0.le
  calc (m : ℝ) * Real.sqrt ((d : ℝ) / (m : ℝ))
      = Real.sqrt ((m : ℝ) ^ 2) * Real.sqrt ((d : ℝ) / (m : ℝ)) := by rw [hsq]
    _ = Real.sqrt (((m : ℝ) ^ 2) * ((d : ℝ) / (m : ℝ))) := by
          rw [Real.sqrt_mul (by positivity)]
    _ = Real.sqrt ((d : ℝ) * (m : ℝ)) := by
          congr 1
          field_simp

/-- For positive `m`, there is a natural blocking parameter `k ≥ 1` whose ceiling-division cost
is at most `2 * √(d * m) + m + 2`. -/
theorem qrom_balanced (d m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, 1 ≤ k ∧
      (ceilDiv d k : ℝ) + (m : ℝ) * ((k : ℝ) - 1) ≤
        2 * Real.sqrt ((d : ℝ) * (m : ℝ)) + (m : ℝ) + 2 := by
  by_cases hd : d = 0
  · refine ⟨1, le_rfl, ?_⟩
    subst hd
    simp [ceilDiv]
    positivity
  · have hd0 : 0 < d := Nat.pos_of_ne_zero hd
    let s : ℝ := Real.sqrt ((d : ℝ) / (m : ℝ))
    let k : ℕ := max 1 ⌈s⌉₊
    have hk1 : 1 ≤ k := le_max_left _ _
    refine ⟨k, hk1, ?_⟩
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hks : s ≤ (k : ℝ) := by
      have h1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
      have h2 : (⌈s⌉₊ : ℝ) ≤ (k : ℝ) := by
        have : ⌈s⌉₊ ≤ k := le_max_right _ _
        exact_mod_cast this
      linarith
    have hk_le : (k : ℝ) ≤ s + 1 := by
      have hkcast : (k : ℝ) = max (1 : ℝ) (⌈s⌉₊ : ℝ) := by
        simp [k, Nat.cast_max]
      rw [hkcast]
      apply max_le
      · linarith
      · linarith [Nat.ceil_lt_add_one hs0]
    have hmunit : (m : ℝ) * ((k : ℝ) - 1) ≤ Real.sqrt ((d : ℝ) * (m : ℝ)) := by
      have h1 : (k : ℝ) - 1 ≤ Real.sqrt ((d : ℝ) / (m : ℝ)) := by
        have hsdef : s = Real.sqrt ((d : ℝ) / (m : ℝ)) := rfl
        linarith [hks]
      have h2 : (m : ℝ) * ((k : ℝ) - 1) ≤ (m : ℝ) * Real.sqrt ((d : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rwa [m_mul_sqrt_div d m hm] at h2
    have hceil : (ceilDiv d k : ℝ) ≤ Real.sqrt ((d : ℝ) * (m : ℝ)) + 1 := by
      have h1 : (ceilDiv d k : ℝ) ≤ (d : ℝ) / (k : ℝ) + 1 := ceilDiv_cast_le d k hk1
      have h2 : (d : ℝ) / (k : ℝ) ≤ (d : ℝ) / s :=
        div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (d : ℝ))
          (Real.sqrt_pos.mpr (by positivity)) hks
      have h3 : (d : ℝ) / s = Real.sqrt ((d : ℝ) * (m : ℝ)) := by
        have hsdef : s = Real.sqrt ((d : ℝ) / (m : ℝ)) := rfl
        rw [hsdef]
        exact sqrt_div_self d m hd0 hm
      linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith

/-- The logarithmic scale `Nat.clog 2 (N + 3) + 1` used in the resource estimates. -/
def Lstar (N : ℕ) : ℕ := Nat.clog 2 (N + 3) + 1

/-- The logarithmic scale `Lstar N` is at least one. -/
theorem one_le_Lstar (N : ℕ) : 1 ≤ Lstar N := by
  unfold Lstar
  have : 0 ≤ Nat.clog 2 (N + 3) := Nat.zero_le _
  omega

/-- For base `b > 1`, the natural ceiling logarithm of a product is at most the sum of the
ceiling logarithms of its factors. -/
theorem clog_mul_le (b x y : ℕ) (hb : 1 < b) :
    Nat.clog b (x * y) ≤ Nat.clog b x + Nat.clog b y := by
  rw [Nat.clog_le_iff_le_pow hb]
  calc x * y ≤ b ^ Nat.clog b x * b ^ Nat.clog b y :=
        Nat.mul_le_mul (Nat.le_pow_clog hb x) (Nat.le_pow_clog hb y)
    _ = b ^ (Nat.clog b x + Nat.clog b y) := by rw [pow_add]

/-- The natural ceiling logarithm to base two of `L` is at most `L`. -/
theorem clog_self_le (L : ℕ) : Nat.clog 2 L ≤ L := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact Nat.lt_two_pow_self.le

/-- If `M ≤ (N + 1) * Lstar N`, then the register size `nOf M` is at most `2 * Lstar N`. -/
theorem nOf_le_two_Lstar (N M : ℕ) (hM : M ≤ (N + 1) * Lstar N) :
    nOf M ≤ 2 * Lstar N := by
  have hL1 : 1 ≤ Lstar N := one_le_Lstar N
  have h1 : M + 1 ≤ (N + 2) * Lstar N := by
    have h2 : M + 1 ≤ (N + 1) * Lstar N + 1 := Nat.succ_le_succ hM
    have h3 : (N + 1) * Lstar N + 1 ≤ (N + 2) * Lstar N := by
      have h4 : (N + 2) * Lstar N = (N + 1) * Lstar N + Lstar N := by ring
      omega
    omega
  have h2 : Nat.clog 2 (M + 1) ≤ Nat.clog 2 ((N + 2) * Lstar N) :=
    Nat.clog_mono_right 2 h1
  have h3 : Nat.clog 2 ((N + 2) * Lstar N)
      ≤ Nat.clog 2 (N + 2) + Nat.clog 2 (Lstar N) :=
    clog_mul_le 2 (N + 2) (Lstar N) (by norm_num)
  have h4 : Nat.clog 2 (Lstar N) ≤ Lstar N := clog_self_le (Lstar N)
  have h5 : Nat.clog 2 (N + 2) + Lstar N ≤ 2 * Lstar N := by
    have hmono : Nat.clog 2 (N + 2) ≤ Nat.clog 2 (N + 3) :=
      Nat.clog_mono_right 2 (by omega)
    unfold Lstar at *
    omega
  unfold nOf
  omega

/-- If `M ≤ (N + 1) * Lstar N` and `ℵ ≤ Lstar N`, then `mOf M ℵ` is at most `7 * Lstar N`. -/
theorem mOf_le_seven_Lstar (N M ℵ : ℕ) (hM : M ≤ (N + 1) * Lstar N)
    (hℵ : ℵ ≤ Lstar N) : mOf M ℵ ≤ 7 * Lstar N := by
  unfold mOf
  have hn : nOf M ≤ 2 * Lstar N := nOf_le_two_Lstar N M hM
  have hL1 : 1 ≤ Lstar N := one_le_Lstar N
  have hZ : 2 * (nOf M : ℤ) + 2 + (ℵ : ℤ) ≤ 7 * (Lstar N : ℤ) := by
    have hnz : (nOf M : ℤ) ≤ 2 * (Lstar N : ℤ) := by exact_mod_cast hn
    have haz : (ℵ : ℤ) ≤ (Lstar N : ℤ) := by exact_mod_cast hℵ
    have hLz : (1 : ℤ) ≤ (Lstar N : ℤ) := by exact_mod_cast hL1
    linarith
  exact_mod_cast hZ

set_option maxHeartbeats 1000000 in

/-- Under the stated resource-size hypotheses, there are four positive QROM blocking parameters
for which the step cost is nonnegative and at most `200 * (N + 1) * (Lstar N)^3`. -/
theorem exists_step_cost_polylog (N M br ℵ i d : ℕ)
    (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ (N + 1) * Lstar N)
    (hbr : br ≤ Lstar N) (hℵ : ℵ ≤ Lstar N) (hi2 : 2 ≤ i) (hi : i ≤ Lstar N)
    (hd : d ≤ ((N + 1) * Lstar N) ^ 2) :
    ∃ ks1 ks2 kr1 kr2 : ℕ,
      1 ≤ ks1 ∧ 1 ≤ ks2 ∧ 1 ≤ kr1 ∧ 1 ≤ kr2 ∧
      0 ≤ (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ) ∧
      (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ)
        ≤ 200 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
  have hL1 : 1 ≤ Lstar N := one_le_Lstar N
  have hLR1 : (1 : ℝ) ≤ (Lstar N : ℝ) := by exact_mod_cast hL1
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hnR : (nOf M : ℝ) ≤ 2 * (Lstar N : ℝ) := by
    exact_mod_cast nOf_le_two_Lstar N M hM
  have hmR : (mOf M ℵ : ℝ) ≤ 7 * (Lstar N : ℝ) := by
    exact_mod_cast mOf_le_seven_Lstar N M ℵ hM hℵ
  have hbrR : (br : ℝ) ≤ (Lstar N : ℝ) := by exact_mod_cast hbr
  have hℵR : (ℵ : ℝ) ≤ (Lstar N : ℝ) := by exact_mod_cast hℵ
  have hiR : (i : ℝ) ≤ (Lstar N : ℝ) := by exact_mod_cast hi
  have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
  have hMR : (M : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := by exact_mod_cast hM
  have hdR : (d : ℝ) ≤ (((N : ℝ) + 1) * (Lstar N : ℝ)) ^ 2 := by exact_mod_cast hd
  have hmpos : 0 < mOf M ℵ := by
    unfold mOf
    have : 0 ≤ nOf M := Nat.zero_le _
    omega
  have hnpos : 0 < nOf M := by
    unfold nOf
    exact Nat.clog_pos (by norm_num) (by omega)

  obtain ⟨ks1, hks1, hq1⟩ := qrom_balanced d (mOf M ℵ) hmpos
  obtain ⟨ks2, hks2, hq2⟩ := qrom_balanced d 1 (by norm_num)
  obtain ⟨kr1, hkr1, hq3⟩ := qrom_balanced M 1 (by norm_num)
  obtain ⟨kr2, hkr2, hq4⟩ := qrom_balanced M 1 (by norm_num)
  refine ⟨ks1, ks2, kr1, kr2, hks1, hks2, hkr1, hkr2, ?_, ?_⟩
  · unfold stepCost
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one]
    have hn1R : (1 : ℝ) ≤ (nOf M : ℝ) := by
      have h : 1 ≤ nOf M := Nat.succ_le_of_lt hnpos
      exact_mod_cast h
    have hn2 : (1 : ℝ) ≤ (nOf M : ℝ) ^ 2 := by
      nlinarith [hn1R, sq_nonneg ((nOf M : ℝ) - 1)]
    have h0br : (0 : ℝ) ≤ (br : ℝ) := Nat.cast_nonneg br
    have h0ℵ : (0 : ℝ) ≤ (ℵ : ℝ) := Nat.cast_nonneg ℵ
    have h1 : (16 : ℝ) ≤ 30 * (nOf M : ℝ) + 4 * (br : ℝ) + 2 * (nOf M : ℝ) ^ 2
        + 3 * (ℵ : ℝ) := by
      nlinarith [hn1R, hn2, h0br, h0ℵ]
    have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have h4 : ((11 * N / 2 : ℕ) : ℝ) ≤ 2 * (M : ℝ) + 4 * (N : ℝ) * (i : ℝ) := by
      have hcast : ((11 * N / 2 : ℕ) : ℝ) ≤ (11 * (N : ℝ)) / 2 := by
        have h := Nat.cast_div_le (α := ℝ) (m := 11 * N) (n := 2)
        push_cast at h
        exact h
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith [hcast, hM1R, hN0, hi2R]
    have hk1 : (0 : ℝ) ≤ (mOf M ℵ : ℝ) * ((ks1 : ℝ) - 1) := by
      have h0 : (0 : ℝ) ≤ (mOf M ℵ : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ (ks1 : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (ks1 : ℝ) := by exact_mod_cast hks1
        linarith
      exact mul_nonneg h0 h1
    have hc1 : (0 : ℝ) ≤ ((ceilDiv d ks1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc2 : (0 : ℝ) ≤ ((ceilDiv d ks2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc3 : (0 : ℝ) ≤ ((ceilDiv M kr1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc4 : (0 : ℝ) ≤ ((ceilDiv N (2 * kr1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc5 : (0 : ℝ) ≤ ((ceilDiv M kr2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hks2R : (0 : ℝ) ≤ (ks2 : ℝ) := Nat.cast_nonneg _
    have hkr1R : (0 : ℝ) ≤ (kr1 : ℝ) := Nat.cast_nonneg _
    have hkr2R : (0 : ℝ) ≤ (kr2 : ℝ) := Nat.cast_nonneg _
    linarith [h1, h4, hk1, hc1, hc2, hc3, hc4, hc5, hks2R, hkr1R, hkr2R]
  · have hdm : (d : ℝ) * (mOf M ℵ : ℝ)
        ≤ (((N : ℝ) + 1) * (Lstar N : ℝ)) ^ 2 * (7 * (Lstar N : ℝ)) := by
      have h0m : (0 : ℝ) ≤ (mOf M ℵ : ℝ) := Nat.cast_nonneg _
      have h0d : (0 : ℝ) ≤ (((N : ℝ) + 1) * (Lstar N : ℝ)) ^ 2 := by positivity
      exact mul_le_mul hdR hmR h0m h0d
    have hs := Real.sqrt_le_sqrt hdm
    have hsqrt_eq :
        Real.sqrt ((((N : ℝ) + 1) * (Lstar N : ℝ)) ^ 2 * (7 * (Lstar N : ℝ)))
          = ((N : ℝ) + 1) * (Lstar N : ℝ) * Real.sqrt (7 * (Lstar N : ℝ)) := by
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq (by positivity)]
    have hsqrt7 : Real.sqrt (7 * (Lstar N : ℝ)) ≤ 7 * (Lstar N : ℝ) :=
      sqrt_le_self (by linarith)
    have hsqrt_dm : Real.sqrt ((d : ℝ) * (mOf M ℵ : ℝ))
        ≤ 7 * (((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2) := by
      calc Real.sqrt ((d : ℝ) * (mOf M ℵ : ℝ))
          ≤ Real.sqrt ((((N : ℝ) + 1) * (Lstar N : ℝ)) ^ 2 * (7 * (Lstar N : ℝ))) := hs
        _ = ((N : ℝ) + 1) * (Lstar N : ℝ) * Real.sqrt (7 * (Lstar N : ℝ)) := hsqrt_eq
        _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) * (7 * (Lstar N : ℝ)) := by gcongr
        _ = 7 * (((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2) := by ring
    have hsqrt_d : Real.sqrt (d : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := by
      have h := Real.sqrt_le_sqrt hdR
      rwa [Real.sqrt_sq (by positivity)] at h
    have hsqrt_M : Real.sqrt (M : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := by
      have hNL1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := by
        have h := mul_le_mul hNR1 hLR1 (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        linarith [h]
      calc Real.sqrt (M : ℝ) ≤ Real.sqrt (((N : ℝ) + 1) * (Lstar N : ℝ)) :=
            Real.sqrt_le_sqrt hMR
        _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := sqrt_le_self hNL1

    have hLR0 : (0 : ℝ) ≤ (Lstar N : ℝ) := by linarith
    have hLR2 : (1 : ℝ) ≤ (Lstar N : ℝ) ^ 2 := by
      nlinarith [hLR1, sq_nonneg ((Lstar N : ℝ) - 1)]
    have hLle2 : (Lstar N : ℝ) ≤ (Lstar N : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hLR1 hLR0
      nlinarith [h]
    have hLle3 : (Lstar N : ℝ) ≤ (Lstar N : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hLR2 hLR0
      nlinarith [h]
    have hL3ge : (1 : ℝ) ≤ (Lstar N : ℝ) ^ 3 := by
      have h := mul_le_mul hLR2 hLR1 (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (Lstar N : ℝ) ^ 2)
      nlinarith [h]
    have hP1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h := mul_le_mul hNR1 hL3ge (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
      nlinarith [h]
    have hmono : ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2
        ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h0 : (0 : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hLR1 h0
      calc ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2
          = ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 * 1 := by ring
        _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 * (Lstar N : ℝ) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using h
        _ = ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by ring
    have hNL3 : ((N : ℝ) + 1) * (Lstar N : ℝ)
        ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      simpa using mul_le_mul_of_nonneg_left hLle3 h0
    have hNRle : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      simpa using mul_le_mul_of_nonneg_left hL3ge h0
    have hLRsq : (Lstar N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h1 : (Lstar N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 := by
        calc (Lstar N : ℝ) ^ 2 = 1 * (Lstar N : ℝ) ^ 2 := by ring
          _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 := by gcongr
      exact le_trans h1 hmono

    have hLD : (Lstar N : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      linarith [hLle3, hNRle]

    have hQ1 : (ceilDiv d ks1 : ℝ) + (mOf M ℵ : ℝ) * ((ks1 : ℝ) - 1)
        ≤ 23 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h := hq1
      linarith [h, hsqrt_dm, hmono, hmR, hLD, hP1]
    have hQ2 : (ceilDiv d ks2 : ℝ) + (ks2 : ℝ)
        ≤ 6 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h := hq2
      simp only [Nat.cast_one, one_mul, mul_one] at h
      have h' : (ceilDiv d ks2 : ℝ) + (ks2 : ℝ) ≤ 2 * Real.sqrt (d : ℝ) + 4 := by
        linarith
      linarith [h', hsqrt_d, hNL3, hP1]
    have hQ3 : (ceilDiv M kr1 : ℝ) + ((ceilDiv N (2 * kr1) : ℕ) : ℝ) + (kr1 : ℝ)
        ≤ 7 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h := hq3
      simp only [Nat.cast_one, one_mul, mul_one] at h
      have h' : (ceilDiv M kr1 : ℝ) + (kr1 : ℝ) ≤ 2 * Real.sqrt (M : ℝ) + 4 := by
        linarith
      have hN : ((ceilDiv N (2 * kr1) : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
        have hc := ceilDiv_cast_le N (2 * kr1) (by omega)
        push_cast at hc
        have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hk : (1 : ℝ) ≤ 2 * (kr1 : ℝ) := by
          have hk1 : (1 : ℝ) ≤ (kr1 : ℝ) := by exact_mod_cast hkr1
          linarith
        have hdiv : (N : ℝ) / (2 * (kr1 : ℝ)) ≤ (N : ℝ) := div_le_self h0 hk
        have h1 : ((ceilDiv N (2 * kr1) : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by linarith
        linarith [h1, hNRle]
      linarith [h', hsqrt_M, hNL3, hP1, hN]
    have hQ4 : (ceilDiv M kr2 : ℝ) + (kr2 : ℝ)
        ≤ 6 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h := hq4
      simp only [Nat.cast_one, one_mul, mul_one] at h
      have h' : (ceilDiv M kr2 : ℝ) + (kr2 : ℝ) ≤ 2 * Real.sqrt (M : ℝ) + 4 := by
        linarith
      linarith [h', hsqrt_M, hNL3, hP1]
    have hT1 : 30 * (nOf M : ℝ) + 4 * (br : ℝ) - 16 + 2 * (nOf M : ℝ) ^ 2 + 3 * (ℵ : ℝ)
        ≤ 75 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have h0n : (0 : ℝ) ≤ (nOf M : ℝ) := Nat.cast_nonneg _
      have hn2le : (nOf M : ℝ) ^ 2 ≤ 4 * (Lstar N : ℝ) ^ 2 := by
        have h := mul_le_mul hnR hnR h0n (by linarith : (0 : ℝ) ≤ 2 * (Lstar N : ℝ))
        nlinarith [h]
      linarith [hnR, hbrR, hℵR, hn2le, hLRsq, hLD]
    have hT4 : 2 * (M : ℝ) + 4 * ((N : ℝ) * (i : ℝ)) - ((11 * N / 2 : ℕ) : ℝ)
        ≤ 6 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
      have hneg : (0 : ℝ) ≤ ((11 * N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hNi : (N : ℝ) * (i : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := by
        have hNle : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
        have h1 : (N : ℝ) * (i : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) :=
          mul_le_mul hNle hiR (Nat.cast_nonneg i) (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        calc (N : ℝ) * (i : ℝ) ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) := h1
          _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 2 := by
              have h0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
              simpa using mul_le_mul_of_nonneg_left hLle2 h0
          _ ≤ ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3 := hmono
      linarith [hneg, hMR, hNi, hNL3]
    have hdecomp : (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ)
        = (30 * (nOf M : ℝ) + 4 * (br : ℝ) - 16 + 2 * (nOf M : ℝ) ^ 2 + 3 * (ℵ : ℝ)
          + ((ceilDiv d ks1 : ℝ) + (mOf M ℵ : ℝ) * ((ks1 : ℝ) - 1))
          + ((ceilDiv d ks2 : ℝ) + (ks2 : ℝ))
          + (2 * (M : ℝ) + 4 * (N : ℝ) * (i : ℝ) - ((11 * N / 2 : ℕ) : ℝ))
          + ((ceilDiv M kr1 : ℝ) + ((ceilDiv N (2 * kr1) : ℕ) : ℝ) + (kr1 : ℝ))
          + ((ceilDiv M kr2 : ℝ) + (kr2 : ℝ))) := by
      unfold stepCost
      simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_ofNat, Int.cast_one]
      ring
    rw [hdecomp]
    linarith [hT1, hT4, hQ1, hQ2, hQ3, hQ4]

/-- Under the stated resource bounds, nonnegative `lam`, and positive `eps`, positive blocking
parameters exist whose total Toffoli cost is at most `(π * lam / (2 * eps) + 1) * (200 * (N
+ 1) * (Lstar N)^3)`. See [LeeEtAl2021]. -/
theorem main_result_total_toffoli (N M br ℵ i d : ℕ) (lam eps : ℝ)
    (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ (N + 1) * Lstar N)
    (hbr : br ≤ Lstar N) (hℵ : ℵ ≤ Lstar N) (hi2 : 2 ≤ i) (hi : i ≤ Lstar N)
    (hd : d ≤ ((N + 1) * Lstar N) ^ 2) (hlam : 0 ≤ lam) (heps : 0 < eps) :
    ∃ ks1 ks2 kr1 kr2 : ℕ,
      1 ≤ ks1 ∧ 1 ≤ ks2 ∧ 1 ≤ kr1 ∧ 1 ≤ kr2 ∧
      (totalToffoli M N br ℵ i d ks1 ks2 kr1 kr2 lam eps : ℝ)
        ≤ (Real.pi * lam / (2 * eps) + 1)
            * (200 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3) := by
  obtain ⟨ks1, ks2, kr1, kr2, h1, h2, h3, h4, h0, hstep⟩ :=
    exists_step_cost_polylog N M br ℵ i d hN hM1 hM hbr hℵ hi2 hi hd
  refine ⟨ks1, ks2, kr1, kr2, h1, h2, h3, h4, ?_⟩
  have hceilarg : (0 : ℝ) ≤ Real.pi * lam / (2 * eps) := by positivity
  have hI : (qpeIterations lam eps : ℝ) ≤ Real.pi * lam / (2 * eps) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hceilarg)
  have hP0 : (0 : ℝ) ≤ Real.pi * lam / (2 * eps) + 1 := by positivity
  have hcast : (totalToffoli M N br ℵ i d ks1 ks2 kr1 kr2 lam eps : ℝ)
      = (qpeIterations lam eps : ℝ) * (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ) := by
    unfold totalToffoli
    push_cast
    ring
  rw [hcast]
  calc (qpeIterations lam eps : ℝ) * (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ)
      ≤ (Real.pi * lam / (2 * eps) + 1)
          * (stepCost M N br ℵ i d ks1 ks2 kr1 kr2 : ℝ) :=
        mul_le_mul_of_nonneg_right hI h0
    _ ≤ (Real.pi * lam / (2 * eps) + 1)
          * (200 * ((N : ℝ) + 1) * (Lstar N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hstep hP0

end Qatlib.Papers.TensorHyper20.MainResults.ToffoliBlockEncoding
