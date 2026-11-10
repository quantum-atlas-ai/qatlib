/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Mathlib.Data.Nat.ChineseRemainder
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

theorem lemma4_jacobiChar_zero (n : ℕ) [NeZero n] (h1 : 1 < n) :
    jacobiCharZMod n 0 = 0 := by
  unfold jacobiCharZMod
  rw [ZMod.val_zero]
  exact jacobiSym.zero_left h1

lemma jacobiCharZMod_mul (n : ℕ) (a b : ZMod n) :
    jacobiCharZMod n (a * b) = jacobiCharZMod n a * jacobiCharZMod n b := by
  unfold jacobiCharZMod
  rw [ZMod.val_mul, Int.natCast_mod]
  rw [← jacobiSym.mod_left ((a.val * b.val : ℕ) : ℤ) n]
  push_cast
  rw [jacobiSym.mul_left]

theorem lemma4_jacobiSum (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) :
    ∑ x : ZMod n, jacobiCharZMod n x = 0 := by
  classical
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hp2 : p ≠ 2 := hn.ne_two_of_dvd_nat hpdvd
  set m := n / p with hm
  have hmul : p * m = n := Nat.mul_div_cancel' hpdvd
  have hp_ne0 : p ≠ 0 := hp.ne_zero
  have hm_ne0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    omega
  haveI : NeZero p := ⟨hp_ne0⟩
  haveI : NeZero m := ⟨hm_ne0⟩
  have hpsq : ¬ p * p ∣ n := (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp
  have hcop : p.Coprime m := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpm
    exact hpsq (by rw [← hmul]; exact mul_dvd_mul_left p hpm)
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one (F := ZMod p) hchar
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop r.val 1
  have hk_cast : (k : ZMod p) = r := by
    rw [show (k : ZMod p) = (r.val : ZMod p) from ?_, ZMod.natCast_zmod_val]
    rw [ZMod.natCast_eq_natCast_iff]
    exact hk1
  have hJp : jacobiSym (k : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    show quadraticChar (ZMod p) ((k : ℤ) : ZMod p) = -1
    push_cast
    rw [hk_cast, hr]
  have hJm : jacobiSym (k : ℤ) m = 1 := by
    have hmod : (k : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) := by
      have h2 : ((k % m : ℕ) : ℤ) = (((1 % m : ℕ)) : ℤ) := by rw [hk2]
      rw [Int.natCast_mod, Int.natCast_mod] at h2
      simpa only [Int.natCast_one] using h2
    rw [jacobiSym.mod_left' hmod]
    exact jacobiSym.one_left m
  have hJn : jacobiSym (k : ℤ) n = -1 := by
    rw [← hmul, jacobiSym.mul_right, hJp, hJm]
    ring
  have hunit : IsUnit (k : ZMod n) := by
    rw [ZMod.isUnit_iff_coprime k n, Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    have hz : jacobiSym (k : ℤ) n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      simpa [Int.gcd_def] using hg
    rw [hJn] at hz
    norm_num at hz
  have huJ : jacobiCharZMod n (k : ZMod n) = -1 := by
    unfold jacobiCharZMod
    rw [ZMod.val_natCast]
    have hcast : ((k % n : ℕ) : ℤ) = (k : ℤ) % (n : ℤ) := Int.natCast_mod k n
    rw [hcast, ← jacobiSym.mod_left (k : ℤ) n]
    exact hJn
  have hbij : Function.Bijective (fun x : ZMod n => (k : ZMod n) * x) := by
    obtain ⟨v, hv⟩ := hunit
    rw [← hv]
    exact v.mulLeft_bijective
  have hS : (∑ x : ZMod n, jacobiCharZMod n x)
      = ∑ x : ZMod n, jacobiCharZMod n ((k : ZMod n) * x) :=
    (Fintype.sum_bijective (fun x : ZMod n => (k : ZMod n) * x) hbij
      (fun x => jacobiCharZMod n ((k : ZMod n) * x))
      (fun x => jacobiCharZMod n x)
      (fun x => rfl)).symm
  have hcalc : (∑ x : ZMod n, jacobiCharZMod n ((k : ZMod n) * x))
      = - ∑ x : ZMod n, jacobiCharZMod n x := by
    simp_rw [jacobiCharZMod_mul]
    rw [← Finset.mul_sum, huJ]
    ring
  have hzero : (∑ x : ZMod n, jacobiCharZMod n x) = 0 := by
    have heq := hS.trans hcalc
    linarith
  exact hzero

end Qatlib.Papers.QuadChar00.MainResults
