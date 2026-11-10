/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAAmplify09.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset

namespace Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma

noncomputable def binomialTerm (ε : ℝ) (r k : ℕ) : ℝ :=
  (Nat.choose r k : ℝ) * ε ^ k * (1 - ε) ^ (r - k)

noncomputable def badMass (ε : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (r / 2 + 1) r, binomialTerm ε r k

noncomputable def medianFailureBound (ε : ℝ) (r : ℕ) : ℝ :=
  (1 / 2) * (2 * Real.sqrt (ε * (1 - ε))) ^ r

theorem two_mul_sum_Icc_choose_le (r : ℕ) :
    2 * (∑ k ∈ Finset.Icc (r / 2 + 1) r, (Nat.choose r k : ℝ)) ≤ (2 : ℝ) ^ r := by
  set m := r / 2 + 1 with hm

  have hIcc : Finset.Icc m r = Finset.Ico m (r + 1) :=
    (Finset.Ico_add_one_right_eq_Icc m r).symm
  have htail_eq_head :
      (∑ k ∈ Finset.Ico m (r + 1), (Nat.choose r k : ℝ)) =
        ∑ k ∈ Finset.Ico 0 (r + 1 - m), (Nat.choose r k : ℝ) := by
    have hh := sum_Ico_reflect (fun j => (Nat.choose r j : ℝ)) m (m := r + 1) (n := r)
      (by omega : r + 1 ≤ r + 1)
    have hsymm : (∑ j ∈ Finset.Ico m (r + 1), (Nat.choose r (r - j) : ℝ)) =
        ∑ j ∈ Finset.Ico m (r + 1), (Nat.choose r j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ r := by
        have := (Finset.mem_Ico.mp hj).2
        omega
      rw [Nat.choose_symm hjle]
    rw [hsymm] at hh
    simpa using hh

  have hdisj : Disjoint (Finset.Ico 0 (r + 1 - m)) (Finset.Ico m (r + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 : x < r + 1 - m := (Finset.mem_Ico.mp hx).2
    have h2 : m ≤ x := (Finset.mem_Ico.mp hy).1
    have h3 : r + 1 - m ≤ m := by omega
    omega
  have hsub : Finset.Ico 0 (r + 1 - m) ∪ Finset.Ico m (r + 1) ⊆ Finset.range (r + 1) := by
    intro x hx
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hx with h | h
    · have := (Finset.mem_Ico.mp h).2
      omega
    · exact (Finset.mem_Ico.mp h).2

  calc 2 * (∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ))
      = 2 * (∑ k ∈ Finset.Ico m (r + 1), (Nat.choose r k : ℝ)) := by rw [hIcc]
    _ = (∑ k ∈ Finset.Ico 0 (r + 1 - m), (Nat.choose r k : ℝ)) +
          ∑ k ∈ Finset.Ico m (r + 1), (Nat.choose r k : ℝ) := by
        rw [htail_eq_head]; ring
    _ = ∑ k ∈ Finset.Ico 0 (r + 1 - m) ∪ Finset.Ico m (r + 1), (Nat.choose r k : ℝ) := by
        rw [Finset.sum_union hdisj]
    _ ≤ ∑ k ∈ Finset.range (r + 1), (Nat.choose r k : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ = (2 : ℝ) ^ r := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

theorem sqrt_pow_add_self {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (Real.sqrt x) ^ (n + n) = x ^ n := by
  rw [pow_add, ← mul_pow, ← sq, Real.sq_sqrt hx]

theorem sqrt_pow_two_mul_add_one {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (Real.sqrt x) ^ (2 * n + 1) = Real.sqrt x * x ^ n := by
  rw [pow_add, pow_mul, Real.sq_sqrt hx, pow_one]
  ring

theorem even_core {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (n : ℕ) :
    ε ^ (n + 1) * (1 - ε) ^ (n - 1) ≤ (ε * (1 - ε)) ^ n := by
  rcases n with _ | n
  · have h : ε ≤ 1 := by linarith
    simpa using h
  · rw [mul_pow, Nat.add_sub_cancel]
    have hfacL : ε ^ (n + 1 + 1) * (1 - ε) ^ n = (ε ^ (n + 1) * (1 - ε) ^ n) * ε := by
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, pow_succ]; ring
    have hfacR : ε ^ (n + 1) * (1 - ε) ^ (n + 1) =
        (ε ^ (n + 1) * (1 - ε) ^ n) * (1 - ε) := by
      rw [pow_succ]; ring
    rw [hfacL, hfacR]
    have hnn : 0 ≤ ε ^ (n + 1) * (1 - ε) ^ n :=
      mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (by linarith : 0 ≤ 1 - ε) _)
    exact mul_le_mul_of_nonneg_left (by linarith) hnn

theorem odd_core {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (n : ℕ) :
    ε ^ (n + 1) * (1 - ε) ^ n ≤
      Real.sqrt (ε * (1 - ε)) * (ε * (1 - ε)) ^ n := by
  have h1ε : 0 ≤ 1 - ε := by linarith
  have hεle : ε ≤ Real.sqrt (ε * (1 - ε)) :=
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε0).symm
      _ ≤ Real.sqrt (ε * (1 - ε)) := Real.sqrt_le_sqrt (by nlinarith)
  rw [mul_pow]
  have hnn : 0 ≤ ε ^ n * (1 - ε) ^ n :=
    mul_nonneg (pow_nonneg hε0 n) (pow_nonneg h1ε n)
  calc ε ^ (n + 1) * (1 - ε) ^ n = ε * (ε ^ n * (1 - ε) ^ n) := by rw [pow_succ']; ring
    _ ≤ Real.sqrt (ε * (1 - ε)) * (ε ^ n * (1 - ε) ^ n) :=
        mul_le_mul_of_nonneg_right hεle hnn

theorem power_le_sqrt_pow {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (r : ℕ) :
    ε ^ (r / 2 + 1) * (1 - ε) ^ (r - (r / 2 + 1)) ≤
      (Real.sqrt (ε * (1 - ε))) ^ r := by
  have hx0 : 0 ≤ ε * (1 - ε) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  rcases Nat.even_or_odd r with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst hn
    have hhalf : (n + n) / 2 + 1 = n + 1 := by omega
    have hrm : n + n - (n + 1) = n - 1 := by omega
    rw [hhalf, hrm, sqrt_pow_add_self hx0]
    exact even_core hε0 hε1 n
  · subst hn
    have hhalf : (2 * n + 1) / 2 + 1 = n + 1 := by omega
    have hrm : 2 * n + 1 - (n + 1) = n := by omega
    rw [hhalf, hrm, sqrt_pow_two_mul_add_one hx0]
    exact odd_core hε0 hε1 n

theorem median_failure_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (r : ℕ) :
    badMass ε r ≤ medianFailureBound ε r := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    unfold badMass medianFailureBound
    simp
  have hmle : r / 2 + 1 ≤ r := by omega
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  set t : ℝ := ε / (1 - ε) with ht_def
  have ht0 : 0 ≤ t := div_nonneg hε0 h1ε.le
  have ht1 : t ≤ 1 := by rw [ht_def, div_le_one h1ε]; linarith
  set m := r / 2 + 1 with hm

  have hterm : ∀ k ∈ Finset.Icc m r,
      binomialTerm ε r k = (1 - ε) ^ r * ((Nat.choose r k : ℝ) * t ^ k) := by
    intro k hk
    have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
    have hmul : ε = t * (1 - ε) := by rw [ht_def]; field_simp
    have hpow : ε ^ k * (1 - ε) ^ (r - k) = (1 - ε) ^ r * t ^ k := by
      have hk' : k + (r - k) = r := Nat.add_sub_cancel' hkr
      calc ε ^ k * (1 - ε) ^ (r - k) = (t * (1 - ε)) ^ k * (1 - ε) ^ (r - k) := by rw [← hmul]
        _ = t ^ k * (1 - ε) ^ k * (1 - ε) ^ (r - k) := by rw [mul_pow]
        _ = t ^ k * ((1 - ε) ^ k * (1 - ε) ^ (r - k)) := by ring
        _ = t ^ k * (1 - ε) ^ r := by rw [← pow_add, hk']
        _ = (1 - ε) ^ r * t ^ k := by ring
    unfold binomialTerm
    calc (Nat.choose r k : ℝ) * ε ^ k * (1 - ε) ^ (r - k)
        = (Nat.choose r k : ℝ) * (ε ^ k * (1 - ε) ^ (r - k)) := by ring
      _ = (Nat.choose r k : ℝ) * ((1 - ε) ^ r * t ^ k) := by rw [hpow]
      _ = (1 - ε) ^ r * ((Nat.choose r k : ℝ) * t ^ k) := by ring
  have hstep : badMass ε r =
      (1 - ε) ^ r * ∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) * t ^ k := by
    unfold badMass
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm

  have hsplit : (∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) * t ^ k) =
      t ^ m * ∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) * t ^ (k - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hmk : m ≤ k := (Finset.mem_Icc.mp hk).1
    have : t ^ k = t ^ m * t ^ (k - m) := by
      rw [← pow_add, Nat.add_sub_of_le hmk]
    rw [this]; ring

  have hshift : (∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) * t ^ (k - m)) ≤
      ∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hpow : t ^ (k - m) ≤ 1 := pow_le_one₀ ht0 ht1
    have hc : (0:ℝ) ≤ (Nat.choose r k : ℝ) := Nat.cast_nonneg _
    simpa using mul_le_mul_of_nonneg_left hpow hc

  have hcount : (∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ)) ≤ (2:ℝ) ^ r / 2 := by
    have h := two_mul_sum_Icc_choose_le r
    rw [← hm] at h
    linarith

  have hnonneg : 0 ≤ (1 - ε) ^ r * t ^ m := by positivity
  rw [hstep, hsplit, ← mul_assoc]
  calc ((1 - ε) ^ r * t ^ m) * ∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) * t ^ (k - m)
      ≤ ((1 - ε) ^ r * t ^ m) * ∑ k ∈ Finset.Icc m r, (Nat.choose r k : ℝ) :=
        mul_le_mul_of_nonneg_left hshift hnonneg
    _ ≤ ((1 - ε) ^ r * t ^ m) * ((2:ℝ) ^ r / 2) :=
        mul_le_mul_of_nonneg_left hcount hnonneg
    _ ≤ medianFailureBound ε r := by
        unfold medianFailureBound
        have hfac : (1 - ε) ^ r * t ^ m = ε ^ m * (1 - ε) ^ (r - m) := by
          have hsplit' : (1 - ε) ^ r = (1 - ε) ^ (r - m) * (1 - ε) ^ m := by
            rw [← pow_add, Nat.sub_add_cancel hmle]
          have hcancel : (1 - ε) * t = ε := by
            rw [ht_def]; field_simp
          calc (1 - ε) ^ r * t ^ m
              = ((1 - ε) ^ (r - m) * (1 - ε) ^ m) * t ^ m := by rw [hsplit']
            _ = (1 - ε) ^ (r - m) * ((1 - ε) ^ m * t ^ m) := by ring
            _ = (1 - ε) ^ (r - m) * ((1 - ε) * t) ^ m := by rw [← mul_pow]
            _ = (1 - ε) ^ (r - m) * ε ^ m := by rw [hcancel]
            _ = ε ^ m * (1 - ε) ^ (r - m) := by ring
        rw [hfac]
        have hcore := power_le_sqrt_pow hε0 hε1 r
        rw [← hm] at hcore
        have hR : (1/2) * (2 * Real.sqrt (ε * (1 - ε))) ^ r =
            (Real.sqrt (ε * (1 - ε))) ^ r * ((2:ℝ) ^ r / 2) := by
          rw [mul_pow]; ring
        rw [hR]
        exact mul_le_mul_of_nonneg_right hcore (by positivity)

theorem median_failure_bound_eps16 (r : ℕ) :
    medianFailureBound (1/16) r ≤ (2:ℝ) ^ (-(r : ℤ)) := by
  unfold medianFailureBound

  have hbase_le : 2 * Real.sqrt ((1:ℝ) / 16 * (1 - 1/16)) ≤ 1 / 2 := by
    have h : (1:ℝ) / 16 * (1 - 1/16) = 15 / 256 := by norm_num
    rw [h]
    have h2 : Real.sqrt ((15:ℝ) / 256) ≤ 1 / 4 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    linarith
  have hpow : (2 * Real.sqrt ((1:ℝ) / 16 * (1 - 1/16))) ^ r ≤ (1/2 : ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) hbase_le r
  have hz : (2:ℝ) ^ (-(r : ℤ)) = (1/2 : ℝ) ^ r := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  rw [hz]
  calc (1/2) * (2 * Real.sqrt ((1:ℝ) / 16 * (1 - 1/16))) ^ r
      ≤ (1/2) * (1/2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = (1/2 : ℝ) ^ (r + 1) := by rw [pow_succ']
    _ ≤ (1/2 : ℝ) ^ r :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ r)

end Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma
