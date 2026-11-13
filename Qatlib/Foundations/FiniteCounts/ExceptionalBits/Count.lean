/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Counting exceptional binary doubling events

This module defines binary prefix values and the finite set `ExceptionalDoublingScalars` of bit
strings with a selected bit whose offset prefix is congruent to the corresponding power of two.
Prefix reconstruction and congruence counts give `exceptionalDoubling_count_le`.

When the modulus has the prescribed binary width, the tail contribution simplifies to an
additive constant eight in `exceptionalDoubling_card_le_eight`. The motivating scalar-arithmetic
setting is quantum resource estimation for elliptic-curve discrete logarithms
[RoettelerEtAl2017].

## Main statements

* `ExceptionalDoublingScalars`: The bit strings having a true bit at some position `i` with `a +
  prefixValue k i` congruent to `2^i` modulo `r`.
* `exceptionalDoubling_count_le`: For positive `n` and `1 ≤ a < r`, the exceptional count is at
  most `2^(n - Nat.clog 2 a)` plus the sum of `((2^i - a) / r) * 2^(n-i)` from `Nat.clog 2 r` to
  `n`.
* `exceptionalDoubling_card_le_eight`: If `n ≥ 1`, `1 ≤ a < r`, and `r ≥ 2^(n-1)`, there are at
  most `2^(n - Nat.clog 2 a) + 8` exceptional strings.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Foundations.FiniteCounts.ExceptionalBits

open Finset

/-- The natural-number value of bit `j`, extended by zero beyond the bit string. -/
def bitAt {n : ℕ} (k : Fin (n + 1) → Bool) (j : ℕ) : ℕ :=
  if h : j < n + 1 then (if k ⟨j, h⟩ then 1 else 0) else 0

/-- The integer represented by the first `i` bits, with bit `j` weighted by `2^j`. -/
def prefixValue {n : ℕ} (k : Fin (n + 1) → Bool) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, bitAt k j * 2 ^ j

/-- The bit strings having a true bit at some position `i` with `a + prefixValue k i` congruent
to `2^i` modulo `r`. -/
noncomputable def ExceptionalDoublingScalars (n a r : ℕ) : Finset (Fin (n + 1) → Bool) :=
  Finset.univ.filter (fun k : Fin (n + 1) → Bool =>
    ∃ i : Fin (n + 1),
      k i = true ∧ (a + prefixValue k (i : ℕ)) % r = (2 ^ (i : ℕ)) % r)

/-- At an in-range index, `bitAt` is one for a true bit and zero for a false bit. -/
private theorem bitAt_eq_if {n : ℕ} (k : Fin (n + 1) → Bool) {j : ℕ} (hj : j < n + 1) :
    bitAt k j = if k ⟨j, hj⟩ then 1 else 0 := by
  rw [bitAt]
  exact dif_pos hj

/-- Every value of `bitAt` is at most one. -/
private theorem bitAt_le_one {n : ℕ} (k : Fin (n + 1) → Bool) (j : ℕ) : bitAt k j ≤ 1 := by
  rw [bitAt]
  split_ifs <;> omega

/-- At an in-range index, `bitAt` equals one exactly when the corresponding Boolean bit is true. -/
private theorem bitAt_eq_one_iff {n : ℕ} (k : Fin (n + 1) → Bool) {j : ℕ} (hj : j < n + 1) :
    bitAt k j = 1 ↔ k ⟨j, hj⟩ = true := by
  rw [bitAt_eq_if k hj]
  cases k ⟨j, hj⟩ <;> simp

/-- The sum of the first `i` powers of two equals `2^i - 1`. -/
private theorem sum_range_pow_two (i : ℕ) : ∑ j ∈ Finset.range i, 2 ^ j = 2 ^ i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpos : 0 < 2 ^ i := pow_pos (by norm_num) i
    omega

/-- The value of an `i`-bit prefix is strictly smaller than `2^i`. -/
private theorem prefixValue_lt {n : ℕ} (k : Fin (n + 1) → Bool) (i : ℕ) :
    prefixValue k i < 2 ^ i := by
  have hle : prefixValue k i ≤ ∑ j ∈ Finset.range i, 2 ^ j := by
    unfold prefixValue
    apply Finset.sum_le_sum
    intro j _
    calc bitAt k j * 2 ^ j ≤ 1 * 2 ^ j := Nat.mul_le_mul_right _ (bitAt_le_one k j)
      _ = 2 ^ j := one_mul _
  rw [sum_range_pow_two] at hle
  have hpos : 0 < 2 ^ i := pow_pos (by norm_num) i
  omega

/-- Extending a prefix by one bit adds that bit times its power of two. -/
private theorem prefixValue_succ {n : ℕ} (k : Fin (n + 1) → Bool) (i : ℕ) :
    prefixValue k (i + 1) = prefixValue k i + bitAt k i * 2 ^ i := by
  unfold prefixValue
  rw [Finset.sum_range_succ]

/-- A prefix of length `j + t` splits into its first `j` bits and a shifted block of `t` bits. -/
private theorem prefixValue_add_mul {n : ℕ} (k : Fin (n + 1) → Bool) (j t : ℕ) :
    prefixValue k (j + t) = prefixValue k j +
      (∑ u ∈ Finset.range t, bitAt k (j + u) * 2 ^ u) * 2 ^ j := by
  change (∑ u ∈ Finset.range (j + t), bitAt k u * 2 ^ u) =
    prefixValue k j + (∑ u ∈ Finset.range t, bitAt k (j + u) * 2 ^ u) * 2 ^ j
  rw [Finset.sum_range_add, Finset.sum_mul]
  rw [show (∑ u ∈ Finset.range j, bitAt k u * 2 ^ u) = prefixValue k j from rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [pow_add]
  ring

/-- Reducing an `i`-bit prefix modulo `2^j` recovers the `j`-bit prefix when `j ≤ i`. -/
private theorem prefixValue_mod {n : ℕ} (k : Fin (n + 1) → Bool) {j i : ℕ} (h : j ≤ i) :
    prefixValue k i % 2 ^ j = prefixValue k j := by
  rw [show i = j + (i - j) by omega]
  rw [prefixValue_add_mul k j (i - j), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (prefixValue_lt k j)]

/-- Dividing an `i`-bit prefix by `2^j` and reducing modulo two extracts bit `j` when `j < i`. -/
private theorem prefixValue_div {n : ℕ} (k : Fin (n + 1) → Bool) {j i : ℕ} (h : j < i) :
    prefixValue k i / 2 ^ j % 2 = bitAt k j := by
  have hi : i = (j + 1) + (i - (j + 1)) := by omega
  rw [hi]
  have h1 : prefixValue k (j + 1 + (i - (j + 1))) = prefixValue k (j + 1) +
      (∑ u ∈ Finset.range (i - (j + 1)), bitAt k (j + 1 + u) * 2 ^ u) * 2 ^ (j + 1) :=
    prefixValue_add_mul k (j + 1) (i - (j + 1))
  rw [h1, prefixValue_succ k j]
  have h3 : (∑ u ∈ Finset.range (i - (j + 1)), bitAt k (j + 1 + u) * 2 ^ u) * 2 ^ (j + 1) =
      (2 * (∑ u ∈ Finset.range (i - (j + 1)), bitAt k (j + 1 + u) * 2 ^ u)) * 2 ^ j := by
    rw [pow_succ]
    ring
  rw [h3]
  have harith : prefixValue k j + bitAt k j * 2 ^ j +
      (2 * (∑ u ∈ Finset.range (i - (j + 1)), bitAt k (j + 1 + u) * 2 ^ u)) * 2 ^ j =
      prefixValue k j + (bitAt k j +
        2 * (∑ u ∈ Finset.range (i - (j + 1)), bitAt k (j + 1 + u) * 2 ^ u)) * 2 ^ j := by
    ring
  rw [harith, Nat.add_mul_div_right _ _ (pow_pos (by norm_num : (0:ℕ) < 2) j)]
  rw [Nat.div_eq_of_lt (prefixValue_lt k j), Nat.zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := bitAt_le_one k j
  omega

/-- For positive `a` and `m > Nat.clog 2 a`, reducing `2^m - a` modulo `2^(Nat.clog 2 a)` gives
`2^(Nat.clog 2 a) - a`. -/
private theorem pow_sub_clog_mod (a m : ℕ) (ha : 1 ≤ a) (hm : Nat.clog 2 a < m) :
    (2 ^ m - a) % 2 ^ Nat.clog 2 a = 2 ^ Nat.clog 2 a - a := by
  have ha_le : a ≤ 2 ^ Nat.clog 2 a := Nat.le_pow_clog (by norm_num) a
  have he : 1 ≤ m - Nat.clog 2 a := by omega
  have hm_eq : m = Nat.clog 2 a + (m - Nat.clog 2 a) := by omega
  have hpow : 2 ^ m = 2 ^ Nat.clog 2 a * 2 ^ (m - Nat.clog 2 a) := by
    nth_rewrite 1 [hm_eq]
    rw [pow_add]
  have hXle : 2 ^ Nat.clog 2 a ≤ 2 ^ Nat.clog 2 a * 2 ^ (m - Nat.clog 2 a) :=
    Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  have hdecomp : 2 ^ m - a = (2 ^ Nat.clog 2 a - a) +
      2 ^ Nat.clog 2 a * (2 ^ (m - Nat.clog 2 a) - 1) := by
    rw [hpow, Nat.mul_sub_left_distrib, mul_one]
    omega
  rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have hpos : 0 < 2 ^ Nat.clog 2 a := pow_pos (by norm_num) _
  omega

/-- If a prefix equals `2^m - a` with positive `a` and `m > Nat.clog 2 a`, its bit at `Nat.clog
2 a` is one and its shorter prefix equals `2^(Nat.clog 2 a) - a`. -/
private theorem prefixValue_clog_eq {n a : ℕ} (k : Fin (n + 1) → Bool) {m : ℕ}
    (ha : 1 ≤ a) (hm : Nat.clog 2 a < m) (hpre : prefixValue k m = 2 ^ m - a) :
    bitAt k (Nat.clog 2 a) = 1 ∧ prefixValue k (Nat.clog 2 a) = 2 ^ Nat.clog 2 a - a := by
  have hmle : Nat.clog 2 a ≤ m := le_of_lt hm
  have hmod := prefixValue_mod k hmle
  have hp : prefixValue k (Nat.clog 2 a) = 2 ^ Nat.clog 2 a - a := by
    rw [← hmod, hpre, pow_sub_clog_mod a m ha hm]
  refine ⟨?_, hp⟩
  have hdiv := prefixValue_div k hm
  have ha_le : a ≤ 2 ^ Nat.clog 2 a := Nat.le_pow_clog (by norm_num) a
  have hm_eq : m = Nat.clog 2 a + (m - Nat.clog 2 a) := by omega
  have hpow : 2 ^ m = 2 ^ Nat.clog 2 a * 2 ^ (m - Nat.clog 2 a) := by
    nth_rewrite 1 [hm_eq]
    rw [pow_add]
  have hXle : 2 ^ Nat.clog 2 a ≤ 2 ^ Nat.clog 2 a * 2 ^ (m - Nat.clog 2 a) :=
    Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  have hdecomp : 2 ^ m - a = (2 ^ Nat.clog 2 a - a) +
      2 ^ Nat.clog 2 a * (2 ^ (m - Nat.clog 2 a) - 1) := by
    rw [hpow, Nat.mul_sub_left_distrib, mul_one]
    omega
  have hquot : (2 ^ m - a) / 2 ^ Nat.clog 2 a = 2 ^ (m - Nat.clog 2 a) - 1 := by
    rw [hdecomp, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) _),
      Nat.div_eq_of_lt]
    · omega
    · have hpos : 0 < 2 ^ Nat.clog 2 a := pow_pos (by norm_num) _
      omega
  rw [← hdiv, hpre, hquot]
  have he : 1 ≤ m - Nat.clog 2 a := by omega
  have hXpos : 0 < 2 ^ (m - Nat.clog 2 a - 1) := pow_pos (by norm_num) _
  have hpow2 : 2 ^ (m - Nat.clog 2 a) = 2 * 2 ^ (m - Nat.clog 2 a - 1) := by
    conv_lhs => rw [show m - Nat.clog 2 a = (m - Nat.clog 2 a - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hodd : 2 ^ (m - Nat.clog 2 a) - 1 = 2 * (2 ^ (m - Nat.clog 2 a - 1) - 1) + 1 := by
    omega
  rw [hodd, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  omega

/-- The exceptional event at position `m`: the bit is one and the offset prefix is congruent to
`2^m` modulo `r`. -/
@[reducible] private def eventAt (n a r m : ℕ) (k : Fin (n + 1) → Bool) : Prop :=
  bitAt k m = 1 ∧ (a + prefixValue k m) % r = (2 ^ m) % r

/-- The finite set of bit strings satisfying the exceptional event at position `m`. -/
private def eventScalars (n a r m : ℕ) : Finset (Fin (n + 1) → Bool) :=
  Finset.univ.filter (eventAt n a r m)

/-- The finite set of bit strings whose length-`m` prefix equals `2^m - a`. -/
private def extremalScalars (n a _r m : ℕ) : Finset (Fin (n + 1) → Bool) :=
  Finset.univ.filter (fun k => prefixValue k m = 2 ^ m - a)

/-- The finite set of bit strings with bit one at `Nat.clog 2 a` and prefix `2^(Nat.clog 2 a) -
a` at that position. -/
private def clogScalars (n a : ℕ) : Finset (Fin (n + 1) → Bool) :=
  Finset.univ.filter (fun k =>
    bitAt k (Nat.clog 2 a) = 1 ∧ prefixValue k (Nat.clog 2 a) = 2 ^ Nat.clog 2 a - a)

/-- A bit string is exceptional exactly when it satisfies an exceptional event at some in-range
position. -/
private theorem mem_exceptional_iff (n a r : ℕ) (k : Fin (n + 1) → Bool) :
    k ∈ ExceptionalDoublingScalars n a r ↔
      ∃ i : Fin (n + 1), eventAt n a r i.val k := by
  unfold ExceptionalDoublingScalars eventAt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hcong⟩
    exact ⟨i, (bitAt_eq_one_iff k i.isLt).mpr hi, hcong⟩
  · rintro ⟨i, hbit, hcong⟩
    exact ⟨i, (bitAt_eq_one_iff k i.isLt).mp hbit, hcong⟩

/-- If `1 ≤ a < r` and the position is below `Nat.clog 2 r`, the prefix congruence forces the
exact equality `a + prefixValue k i = 2^i`. -/
private theorem event_lt_clog_eq (n a r : ℕ) (k : Fin (n + 1) → Bool) {i : ℕ}
    (ha : 1 ≤ a) (har : a < r) (hi : i < Nat.clog 2 r)
    (hcong : (a + prefixValue k i) % r = (2 ^ i) % r) :
    a + prefixValue k i = 2 ^ i := by
  have hi' : 2 ^ i < r := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp hi
  have ht_mod : (2 ^ i) % r = 2 ^ i := Nat.mod_eq_of_lt hi'
  have hs_mod : (a + prefixValue k i) % r = 2 ^ i := by rw [hcong, ht_mod]
  have hp : prefixValue k i < 2 ^ i := prefixValue_lt k i
  have hrpos : 0 < r := lt_of_lt_of_le ha (le_of_lt har)
  have hs_lt : a + prefixValue k i < 2 ^ i + r := by omega
  have hkey : r * ((a + prefixValue k i) / r) + (a + prefixValue k i) % r = a + prefixValue k i :=
    Nat.div_add_mod _ _
  rw [hs_mod] at hkey
  have hdiv0 : (a + prefixValue k i) / r = 0 := by
    rcases Nat.eq_zero_or_pos ((a + prefixValue k i) / r) with h | h
    · exact h
    · exfalso
      have : r * 1 ≤ r * ((a + prefixValue k i) / r) := Nat.mul_le_mul_left r h
      omega
  rw [hdiv0, Nat.mul_zero, Nat.zero_add] at hkey
  exact hkey.symm

/-- If `1 ≤ a < r`, any position satisfying the prefix congruence is at least `Nat.clog 2 a`. -/
private theorem event_clog_le (n a r : ℕ) (k : Fin (n + 1) → Bool) {j : ℕ}
    (_ha : 1 ≤ a) (har : a < r)
    (hcong : (a + prefixValue k j) % r = (2 ^ j) % r) :
    Nat.clog 2 a ≤ j := by
  by_contra hle
  have hj : j < Nat.clog 2 a := by omega
  have ht_lt_a : 2 ^ j < a := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp hj
  have hp : prefixValue k j < 2 ^ j := prefixValue_lt k j
  have ht_mod : (2 ^ j) % r = 2 ^ j := Nat.mod_eq_of_lt (lt_trans ht_lt_a har)
  have hs_mod : (a + prefixValue k j) % r = 2 ^ j := by rw [hcong, ht_mod]
  have hsub_pos : 0 < (a + prefixValue k j) - 2 ^ j := by omega
  have hsub_lt : (a + prefixValue k j) - 2 ^ j < r := by omega
  have hmod0 : ((a + prefixValue k j) - 2 ^ j) % r = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [hs_mod, ht_mod])
  have hle' : r ≤ (a + prefixValue k j) - 2 ^ j :=
    Nat.le_of_dvd hsub_pos (Nat.dvd_of_mod_eq_zero hmod0)
  omega

/-- The prefix values below `2^m` whose sum with `a` is congruent to `2^m` modulo `r`. -/
private def prefixSolutions (a r m : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ m)).filter (fun p => (a + p) % r = (2 ^ m) % r)

/-- For `1 ≤ a < r`, every prefix solution is at most `2^m - a`. -/
private theorem mem_prefixSolutions_le (a r m : ℕ) (_ha : 1 ≤ a) (har : a < r)
    {p : ℕ} (hp : p ∈ prefixSolutions a r m) : p ≤ 2 ^ m - a := by
  unfold prefixSolutions at hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hcong⟩ := hp
  have hsub_pos_ne : ¬ 2 ^ m < a + p := by
    intro hlt
    have hsub_pos : 0 < (a + p) - 2 ^ m := by omega
    have hsub_lt : (a + p) - 2 ^ m < r := by omega
    have hmod0 : ((a + p) - 2 ^ m) % r = 0 := Nat.sub_mod_eq_zero_of_mod_eq hcong
    have hle' : r ≤ (a + p) - 2 ^ m :=
      Nat.le_of_dvd hsub_pos (Nat.dvd_of_mod_eq_zero hmod0)
    omega
  omega

/-- For `1 ≤ a < r`, each prefix solution is congruent to `2^m - a` modulo `r`. -/
private theorem mem_prefixSolutions_mod (a r m : ℕ) (_ha : 1 ≤ a) (har : a < r)
    {p : ℕ} (hp : p ∈ prefixSolutions a r m) : p % r = (2 ^ m - a) % r := by
  unfold prefixSolutions at hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hcong⟩ := hp
  have ha_le : a ≤ 2 ^ m := by
    by_contra h
    have ht_lt_a : 2 ^ m < a := by omega
    have hsub_pos : 0 < (a + p) - 2 ^ m := by omega
    have hsub_lt : (a + p) - 2 ^ m < r := by omega
    have hmod0 : ((a + p) - 2 ^ m) % r = 0 := Nat.sub_mod_eq_zero_of_mod_eq hcong
    have hle' : r ≤ (a + p) - 2 ^ m :=
      Nat.le_of_dvd hsub_pos (Nat.dvd_of_mod_eq_zero hmod0)
    omega
  have hmodeq : (a + p) ≡ 2 ^ m [MOD r] := hcong
  have hsub := Nat.ModEq.sub' (show a ≤ a + p ↔ a ≤ 2 ^ m by omega) hmodeq (Nat.ModEq.refl a)
  simpa [Nat.add_sub_cancel_left] using! hsub

/-- For `1 ≤ a < r`, there are at most `(2^m - a) / r + 1` prefix solutions. -/
private theorem prefixSolutions_card_le (a r m : ℕ) (ha : 1 ≤ a) (har : a < r) :
    (prefixSolutions a r m).card ≤ (2 ^ m - a) / r + 1 := by
  have hmaps : Set.MapsTo (fun p : ℕ => p / r) ↑(prefixSolutions a r m)
      ↑(Finset.range ((2 ^ m - a) / r + 1)) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_prefixSolutions_le a r m ha har hp))
  have hinj : Set.InjOn (fun p : ℕ => p / r) ↑(prefixSolutions a r m) := by
    intro p hp p' hp' hpp
    have hmod := mem_prefixSolutions_mod a r m ha har hp
    have hmod' := mem_prefixSolutions_mod a r m ha har hp'
    have hrem : p % r = p' % r := by rw [hmod, hmod']
    have hp1 : r * (p / r) + p % r = p := Nat.div_add_mod p r
    have hp2 : r * (p' / r) + p' % r = p' := Nat.div_add_mod p' r
    change p / r = p' / r at hpp
    rw [hpp] at hp1
    omega
  have h := Finset.card_le_card_of_injOn (fun p : ℕ => p / r) hmaps hinj
  rwa [Finset.card_range] at h

/-- For `1 ≤ a < r`, removing `2^m - a` leaves at most `(2^m - a) / r` prefix solutions. -/
private theorem prefixSolutions_erase_card_le (a r m : ℕ) (ha : 1 ≤ a) (har : a < r) :
    ((prefixSolutions a r m).erase (2 ^ m - a)).card ≤ (2 ^ m - a) / r := by
  have hrpos : 0 < r := lt_of_lt_of_le ha (le_of_lt har)
  have hmaps : Set.MapsTo (fun p : ℕ => p / r) ↑((prefixSolutions a r m).erase (2 ^ m - a))
      ↑(Finset.range ((2 ^ m - a) / r)) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_erase] at hp
    obtain ⟨hpne, hpP⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_range]
    have hle := mem_prefixSolutions_le a r m ha har hpP
    have hmod := mem_prefixSolutions_mod a r m ha har hpP
    have hlt : p < 2 ^ m - a := lt_of_le_of_ne hle hpne
    have hq1 : r * ((2 ^ m - a) / r) + (2 ^ m - a) % r = 2 ^ m - a :=
      Nat.div_add_mod _ _
    have hp1 : r * (p / r) + p % r = p := Nat.div_add_mod p r
    have hmul : r * (p / r) < r * ((2 ^ m - a) / r) := by omega
    exact (Nat.mul_lt_mul_left hrpos).mp hmul
  have hinj : Set.InjOn (fun p : ℕ => p / r) ↑((prefixSolutions a r m).erase (2 ^ m - a)) := by
    intro p hp p' hp' hpp
    rw [Finset.mem_coe, Finset.mem_erase] at hp hp'
    have hmod := mem_prefixSolutions_mod a r m ha har hp.2
    have hmod' := mem_prefixSolutions_mod a r m ha har hp'.2
    have hrem : p % r = p' % r := by rw [hmod, hmod']
    have hp1 : r * (p / r) + p % r = p := Nat.div_add_mod p r
    have hp2 : r * (p' / r) + p' % r = p' := Nat.div_add_mod p' r
    change p / r = p' / r at hpp
    rw [hpp] at hp1
    omega
  have h := Finset.card_le_card_of_injOn (fun p : ℕ => p / r) hmaps hinj
  rwa [Finset.card_range] at h

/-- The suffix of a bit string strictly after position `m`. -/
private def tailFun {n : ℕ} (m : ℕ) (k : Fin (n + 1) → Bool) : Fin (n - m) → Bool :=
  fun t => k ⟨m + 1 + t.val, by have := t.isLt; omega⟩

/-- Equality of in-range natural bit values implies equality of the corresponding Boolean bits. -/
private theorem bool_eq_of_bitAt_eq {n : ℕ} (k k' : Fin (n + 1) → Bool) {j : ℕ}
    (hj : j < n + 1) (h : bitAt k j = bitAt k' j) : k ⟨j, hj⟩ = k' ⟨j, hj⟩ := by
  cases hk : k ⟨j, hj⟩ <;> cases hk' : k' ⟨j, hj⟩
  · rfl
  · exfalso
    have h1 : bitAt k j = 0 := by rw [bitAt_eq_if k hj, hk]; rfl
    have h2 : bitAt k' j = 1 := by rw [bitAt_eq_if k' hj, hk']; rfl
    omega
  · exfalso
    have h1 : bitAt k j = 1 := by rw [bitAt_eq_if k hj, hk]; rfl
    have h2 : bitAt k' j = 0 := by rw [bitAt_eq_if k' hj, hk']; rfl
    omega
  · rfl

/-- A bit string is determined by its length-`m` prefix, its bit at `m`, and its suffix after
`m`, provided `m ≤ n`. -/
private theorem eq_of_prefixValue_tail {n : ℕ} (m : ℕ) (k k' : Fin (n + 1) → Bool)
    (hm : m ≤ n) (hp : prefixValue k m = prefixValue k' m)
    (hb : bitAt k m = bitAt k' m)
    (ht : ∀ t : Fin (n - m), tailFun m k t = tailFun m k' t) : k = k' := by
  funext u
  rcases lt_trichotomy u.val m with hlt | heq | hgt
  · have hbit : bitAt k u.val = bitAt k' u.val := by
      rw [← prefixValue_div k hlt, ← prefixValue_div k' hlt, hp]
    simpa using bool_eq_of_bitAt_eq k k' u.isLt hbit
  · have hbit : bitAt k u.val = bitAt k' u.val := by
      rw [heq]; exact hb
    simpa using bool_eq_of_bitAt_eq k k' u.isLt hbit
  · have htlt : u.val - m - 1 < n - m := by omega
    have hk : k u = tailFun m k ⟨u.val - m - 1, htlt⟩ := by
      unfold tailFun
      congr 1
      exact Fin.ext (by simp only []; omega)
    have hk' : k' u = tailFun m k' ⟨u.val - m - 1, htlt⟩ := by
      unfold tailFun
      congr 1
      exact Fin.ext (by simp only []; omega)
    rw [hk, hk']
    exact ht ⟨u.val - m - 1, htlt⟩

/-- For `m ≤ n` and `1 ≤ a < r`, the event set at `m` has cardinality at most `((2^m - a) / r +
1) * 2^(n-m)`. -/
private theorem eventScalars_card_le (n a r m : ℕ) (hm : m ≤ n) (ha : 1 ≤ a) (har : a < r) :
    (eventScalars n a r m).card ≤ ((2 ^ m - a) / r + 1) * 2 ^ (n - m) := by
  have hmaps : Set.MapsTo (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k))
      ↑(eventScalars n a r m)
      ↑((prefixSolutions a r m) ×ˢ (Finset.univ : Finset (Fin (n - m) → Bool))) := by
    intro k hk
    change k ∈ eventScalars n a r m at hk
    unfold eventScalars at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨hbit, hcong⟩ := hk
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true]
    unfold prefixSolutions
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨prefixValue_lt k m, hcong⟩
  have hinj : Set.InjOn (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k))
      ↑(eventScalars n a r m) := by
    intro k hk k' hk' hpair
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨hp, ht⟩ := hpair
    have hbit : bitAt k m = bitAt k' m := by
      have h1 : k ∈ eventScalars n a r m := hk
      have h2 : k' ∈ eventScalars n a r m := hk'
      unfold eventScalars at h1 h2
      rw [Finset.mem_filter] at h1 h2
      simp only [Finset.mem_univ, true_and] at h1 h2
      rw [h1.1, h2.1]
    exact eq_of_prefixValue_tail m k k' hm hp hbit (fun t => congrFun ht t)
  have hcard :=
      Finset.card_le_card_of_injOn
      (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k)) hmaps hinj
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] at hcard
  calc (eventScalars n a r m).card ≤ (prefixSolutions a r m).card * 2 ^ (n - m) := hcard
    _ ≤ ((2 ^ m - a) / r + 1) * 2 ^ (n - m) :=
        Nat.mul_le_mul_right _ (prefixSolutions_card_le a r m ha har)

/-- For `m ≤ n` and `1 ≤ a < r`, removing the extremal-prefix strings bounds the event-set
cardinality by `((2^m - a) / r) * 2^(n-m)`. -/
private theorem eventScalars_diff_card_le (n a r m : ℕ) (hm : m ≤ n) (ha : 1 ≤ a) (har : a < r) :
    ((eventScalars n a r m) \ (extremalScalars n a r m)).card ≤
      ((2 ^ m - a) / r) * 2 ^ (n - m) := by
  have hmaps : Set.MapsTo (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k))
      ↑((eventScalars n a r m) \ (extremalScalars n a r m))
      ↑(((prefixSolutions a r m).erase (2 ^ m - a)) ×ˢ
        (Finset.univ : Finset (Fin (n - m) → Bool))) := by
    intro k hk
    change k ∈ (eventScalars n a r m) \ (extremalScalars n a r m) at hk
    rw [Finset.mem_sdiff] at hk
    obtain ⟨hevent, hext⟩ := hk
    unfold eventScalars at hevent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hevent
    obtain ⟨hbit, hcong⟩ := hevent
    have hpne : prefixValue k m ≠ 2 ^ m - a := by
      intro h
      apply hext
      unfold extremalScalars
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true]
    refine Finset.mem_erase.mpr ⟨hpne, ?_⟩
    unfold prefixSolutions
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨prefixValue_lt k m, hcong⟩
  have hinj : Set.InjOn (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k))
      ↑((eventScalars n a r m) \ (extremalScalars n a r m)) := by
    intro k hk k' hk' hpair
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨hp, ht⟩ := hpair
    have hkE : k ∈ eventScalars n a r m := (Finset.mem_sdiff.mp hk).1
    have hk'E : k' ∈ eventScalars n a r m := (Finset.mem_sdiff.mp hk').1
    have hbit : bitAt k m = bitAt k' m := by
      have h1 := hkE
      have h2 := hk'E
      unfold eventScalars at h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1.1, h2.1]
    exact eq_of_prefixValue_tail m k k' hm hp hbit (fun t => congrFun ht t)
  have hcard :=
      Finset.card_le_card_of_injOn
      (fun k : Fin (n + 1) → Bool => (prefixValue k m, tailFun m k)) hmaps hinj
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] at hcard
  calc ((eventScalars n a r m) \ (extremalScalars n a r m)).card
      ≤ ((prefixSolutions a r m).erase (2 ^ m - a)).card * 2 ^ (n - m) := hcard
    _ ≤ ((2 ^ m - a) / r) * 2 ^ (n - m) :=
        Nat.mul_le_mul_right _ (prefixSolutions_erase_card_le a r m ha har)

/-- If `Nat.clog 2 a ≤ n`, the logarithmic-position set has cardinality at most `2^(n - Nat.clog
2 a)`. -/
private theorem clogScalars_card_le (n a : ℕ) (hm : Nat.clog 2 a ≤ n) :
    (clogScalars n a).card ≤ 2 ^ (n - Nat.clog 2 a) := by
  have hmaps : Set.MapsTo (tailFun (n := n) (Nat.clog 2 a)) ↑(clogScalars n a)
      ↑(Finset.univ : Finset (Fin (n - Nat.clog 2 a) → Bool)) := by
    intro k _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  have hinj : Set.InjOn (tailFun (n := n) (Nat.clog 2 a)) ↑(clogScalars n a) := by
    intro k hk k' hk' ht
    change k ∈ clogScalars n a at hk
    change k' ∈ clogScalars n a at hk'
    unfold clogScalars at hk hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    have hp : prefixValue k (Nat.clog 2 a) = prefixValue k' (Nat.clog 2 a) := by
      rw [hk.2, hk'.2]
    have hbit : bitAt k (Nat.clog 2 a) = bitAt k' (Nat.clog 2 a) := by
      rw [hk.1, hk'.1]
    exact eq_of_prefixValue_tail (Nat.clog 2 a) k k' hm hp hbit (fun t => congrFun ht t)
  have hcard := Finset.card_le_card_of_injOn (tailFun (n := n) (Nat.clog 2 a)) hmaps hinj
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  exact hcard

/-- The exceptional strings possessing an exceptional event below `Nat.clog 2 r`. -/
private noncomputable def smallScalars (n a r : ℕ) : Finset (Fin (n + 1) → Bool) :=
  (ExceptionalDoublingScalars n a r).filter
    (fun k => ∃ j : Fin (n + 1), j.val < Nat.clog 2 r ∧ eventAt n a r j.val k)

/-- The exceptional strings with no exceptional event below `Nat.clog 2 r`. -/
private noncomputable def largeScalars (n a r : ℕ) : Finset (Fin (n + 1) → Bool) :=
  (ExceptionalDoublingScalars n a r).filter
    (fun k => ¬ ∃ j : Fin (n + 1), j.val < Nat.clog 2 r ∧ eventAt n a r j.val k)

/-- The exceptional set is the union of its small-position and remaining parts. -/
private theorem exceptional_eq_small_union_large (n a r : ℕ) :
    ExceptionalDoublingScalars n a r = smallScalars n a r ∪ largeScalars n a r := by
  unfold smallScalars largeScalars
  exact (Finset.filter_union_filter_not_eq _ _).symm

/-- For `1 ≤ a < r`, every small-position exceptional string belongs to the logarithmic-position
set. -/
private theorem smallScalars_subset_clogScalars (n a r : ℕ) (ha : 1 ≤ a) (har : a < r) :
    smallScalars n a r ⊆ clogScalars n a := by
  intro k hk
  unfold smallScalars at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨_hkS, j, hjlt, hjevent⟩ := hk
  obtain ⟨hjbit, hjcong⟩ := hjevent
  have hj_eq : a + prefixValue k j.val = 2 ^ j.val :=
    event_lt_clog_eq n a r k ha har hjlt hjcong
  have hi0_le : Nat.clog 2 a ≤ j.val := event_clog_le n a r k ha har hjcong
  have hpre : prefixValue k j.val = 2 ^ j.val - a := by omega
  unfold clogScalars
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases lt_or_eq_of_le hi0_le with hlt | heq
  · exact prefixValue_clog_eq k ha hlt hpre
  · rw [← heq] at hjbit hpre
    exact ⟨hjbit, hpre⟩

/-- If `1 ≤ a < r` and `Nat.clog 2 a < Nat.clog 2 r`, every remaining exceptional string has a
nonextremal event at a position from `Nat.clog 2 r` through `n`. -/
private theorem largeScalars_subset_biUnion_lt (n a r : ℕ) (ha : 1 ≤ a) (_har : a < r)
    (hlt : Nat.clog 2 a < Nat.clog 2 r) :
    largeScalars n a r ⊆
      (Finset.Icc (Nat.clog 2 r) n).biUnion
        (fun m => eventScalars n a r m \ extremalScalars n a r m) := by
  intro k hk
  unfold largeScalars at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hkS, hkno⟩ := hk
  obtain ⟨j, hjevent⟩ := (mem_exceptional_iff n a r k).mp hkS
  have hjc : Nat.clog 2 r ≤ j.val := by
    by_contra h
    exact hkno ⟨j, by omega, hjevent⟩
  have hjn : j.val ≤ n := by have := j.isLt; omega
  rw [Finset.mem_biUnion]
  refine ⟨j.val, Finset.mem_Icc.mpr ⟨hjc, hjn⟩, ?_⟩
  have hkE : k ∈ eventScalars n a r j.val := by
    unfold eventScalars
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hjevent⟩
  have hkNotP0 : k ∉ extremalScalars n a r j.val := by
    intro hmem
    unfold extremalScalars at hmem
    rw [Finset.mem_filter] at hmem
    have hpre : prefixValue k j.val = 2 ^ j.val - a := hmem.2
    have hi0_lt_j : Nat.clog 2 a < j.val := lt_of_lt_of_le hlt hjc
    have hclog := prefixValue_clog_eq k ha hi0_lt_j hpre
    have hevent0 : eventAt n a r (Nat.clog 2 a) k := by
      refine ⟨hclog.1, ?_⟩
      rw [hclog.2, Nat.add_sub_of_le (Nat.le_pow_clog (by norm_num : 1 < 2) a)]
    have hwit : ∃ j' : Fin (n + 1), j'.val < Nat.clog 2 r ∧ eventAt n a r j'.val k := by
      refine ⟨⟨Nat.clog 2 a, by omega⟩, hlt, ?_⟩
      simpa using hevent0
    exact hkno hwit
  exact Finset.mem_sdiff.mpr ⟨hkE, hkNotP0⟩

/-- If `1 ≤ a < r` and `Nat.clog 2 r ≤ Nat.clog 2 a`, the small-position exceptional set is
empty. -/
private theorem smallScalars_eq_empty_of_le (n a r : ℕ) (ha : 1 ≤ a) (har : a < r)
    (hle : Nat.clog 2 r ≤ Nat.clog 2 a) : smallScalars n a r = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨k, hk⟩
  unfold smallScalars at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨_hkS, j, hjlt, hjevent⟩ := hk
  have := event_clog_le n a r k ha har hjevent.2
  omega

/-- When `1 ≤ a < r` and the logarithmic thresholds are reversed, the remaining exceptional
strings lie in the event set at `Nat.clog 2 a` or in a nonextremal event set at another
position between `Nat.clog 2 r` and `n`, assuming `Nat.clog 2 a ≤ n`. -/
private theorem largeScalars_subset_union_le (n a r : ℕ) (ha : 1 ≤ a) (har : a < r)
    (hle : Nat.clog 2 r ≤ Nat.clog 2 a) (_hi0n : Nat.clog 2 a ≤ n) :
    largeScalars n a r ⊆ eventScalars n a r (Nat.clog 2 a) ∪
      ((Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a)).biUnion
        (fun m => eventScalars n a r m \ extremalScalars n a r m) := by
  intro k hk
  unfold largeScalars at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hkS, _hkno⟩ := hk
  obtain ⟨j, hjevent⟩ := (mem_exceptional_iff n a r k).mp hkS
  have hj0 : Nat.clog 2 a ≤ j.val := event_clog_le n a r k ha har hjevent.2
  have hjn : j.val ≤ n := by have := j.isLt; omega
  rcases lt_or_eq_of_le hj0 with hlt | heq
  · by_cases hpre : prefixValue k j.val = 2 ^ j.val - a
    · rw [Finset.mem_union]
      left
      have hclog := prefixValue_clog_eq k ha hlt hpre
      unfold eventScalars
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hclog.1, ?_⟩
      rw [hclog.2, Nat.add_sub_of_le (Nat.le_pow_clog (by norm_num : 1 < 2) a)]
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_biUnion]
      have hjc : Nat.clog 2 r ≤ j.val := le_trans hle hj0
      refine ⟨j.val, Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hjc, hjn⟩⟩, ?_⟩
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · unfold eventScalars
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hjevent⟩
      · intro hmem
        unfold extremalScalars at hmem
        rw [Finset.mem_filter] at hmem
        exact hpre hmem.2
  · rw [Finset.mem_union]
    left
    unfold eventScalars
    rw [Finset.mem_filter]
    rw [heq]
    exact ⟨Finset.mem_univ _, hjevent⟩

/-- For positive `n` and `1 ≤ a < r`, the exceptional count is at most `2^(n - Nat.clog 2 a)`
plus the sum of `((2^i - a) / r) * 2^(n-i)` from `Nat.clog 2 r` to `n`. -/
theorem exceptionalDoubling_count_le (n a r : ℕ)
    (_hn : 1 ≤ n) (ha : 1 ≤ a) (har : a < r) :
    (ExceptionalDoublingScalars n a r).card ≤
      2 ^ (n - Nat.clog 2 a) +
        ∑ i ∈ Finset.Icc (Nat.clog 2 r) n, ((2 ^ i - a) / r) * 2 ^ (n - i) := by
  by_cases hbig : n < Nat.clog 2 a
  · have hempty : ExceptionalDoublingScalars n a r = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨k, hk⟩
      obtain ⟨j, hjevent⟩ := (mem_exceptional_iff n a r k).mp hk
      have hle := event_clog_le n a r k ha har hjevent.2
      have := j.isLt
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · push Not at hbig
    by_cases hlt : Nat.clog 2 a < Nat.clog 2 r
    · have hS := exceptional_eq_small_union_large n a r
      have hsmall := smallScalars_subset_clogScalars n a r ha har
      have hlarge := largeScalars_subset_biUnion_lt n a r ha har hlt
      calc (ExceptionalDoublingScalars n a r).card
          = (smallScalars n a r ∪ largeScalars n a r).card := by rw [hS]
        _ ≤ (smallScalars n a r).card + (largeScalars n a r).card := Finset.card_union_le _ _
        _ ≤ (clogScalars n a).card +
              ((Finset.Icc (Nat.clog 2 r) n).biUnion
                (fun m => eventScalars n a r m \ extremalScalars n a r m)).card :=
              Nat.add_le_add (Finset.card_le_card hsmall) (Finset.card_le_card hlarge)
        _ ≤ 2 ^ (n - Nat.clog 2 a) +
              ∑ m ∈ Finset.Icc (Nat.clog 2 r) n,
                ((2 ^ m - a) / r) * 2 ^ (n - m) := by
              apply Nat.add_le_add
              · exact clogScalars_card_le n a hbig
              · calc ((Finset.Icc (Nat.clog 2 r) n).biUnion
                      (fun m => eventScalars n a r m \ extremalScalars n a r m)).card
                    ≤ ∑ m ∈ Finset.Icc (Nat.clog 2 r) n,
                        (eventScalars n a r m \ extremalScalars n a r m).card :=
                      Finset.card_biUnion_le
                  _ ≤ ∑ m ∈ Finset.Icc (Nat.clog 2 r) n,
                        ((2 ^ m - a) / r) * 2 ^ (n - m) := by
                      apply Finset.sum_le_sum
                      intro m hm
                      exact eventScalars_diff_card_le n a r m (Finset.mem_Icc.mp hm).2 ha har
    · push Not at hlt
      have hsmall0 := smallScalars_eq_empty_of_le n a r ha har hlt
      have hlarge := largeScalars_subset_union_le n a r ha har hlt hbig
      have hS := exceptional_eq_small_union_large n a r
      rw [hsmall0, Finset.empty_union] at hS
      have hmem : Nat.clog 2 a ∈ Finset.Icc (Nat.clog 2 r) n :=
        Finset.mem_Icc.mpr ⟨hlt, hbig⟩
      have hsplit := Finset.sum_erase_add (Finset.Icc (Nat.clog 2 r) n)
        (fun m => ((2 ^ m - a) / r) * 2 ^ (n - m)) hmem
      calc (ExceptionalDoublingScalars n a r).card
          = (largeScalars n a r).card := by rw [hS]
        _ ≤ (eventScalars n a r (Nat.clog 2 a) ∪
              ((Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a)).biUnion
                (fun m => eventScalars n a r m \ extremalScalars n a r m)).card :=
              Finset.card_le_card hlarge
        _ ≤ (eventScalars n a r (Nat.clog 2 a)).card +
              (((Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a)).biUnion
                (fun m => eventScalars n a r m \ extremalScalars n a r m)).card :=
              Finset.card_union_le _ _
        _ ≤ ((2 ^ Nat.clog 2 a - a) / r + 1) * 2 ^ (n - Nat.clog 2 a) +
              ∑ m ∈ (Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a),
                ((2 ^ m - a) / r) * 2 ^ (n - m) := by
              apply Nat.add_le_add
              · exact eventScalars_card_le n a r (Nat.clog 2 a) hbig ha har
              · calc (((Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a)).biUnion
                      (fun m => eventScalars n a r m \ extremalScalars n a r m)).card
                    ≤ ∑ m ∈ (Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a),
                        (eventScalars n a r m \ extremalScalars n a r m).card :=
                      Finset.card_biUnion_le
                  _ ≤ ∑ m ∈ (Finset.Icc (Nat.clog 2 r) n).erase (Nat.clog 2 a),
                        ((2 ^ m - a) / r) * 2 ^ (n - m) := by
                      apply Finset.sum_le_sum
                      intro m hm
                      exact eventScalars_diff_card_le n a r m
                        (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).2 ha har
        _ = 2 ^ (n - Nat.clog 2 a) +
              ∑ m ∈ Finset.Icc (Nat.clog 2 r) n,
                ((2 ^ m - a) / r) * 2 ^ (n - m) := by
              try dsimp only at hsplit
              rw [Nat.add_mul, one_mul]
              omega

/-- If `n ≥ 1` and `r ≥ 2^(n-1)`, then `Nat.clog 2 r ≥ n - 1`. -/
theorem orderWidth_clog_ge (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ^ (n - 1) ≤ r) :
    n - 1 ≤ Nat.clog 2 r := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with hn1 | hn2
  · rw [hn1]
    omega
  · have hlt : 2 ^ (n - 2) < r := by
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hr
    have h := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
    omega

/-- If `n ≥ 1` and `c ≥ n - 1`, the weighted tail sum from `c` to `n` is at most twice `(2^(n-1)
- a) / r` plus `(2^n - a) / r`. -/
theorem tail_sum_le_two_terms (n a r c : ℕ) (hn : 1 ≤ n) (hc : n - 1 ≤ c) :
    (∑ i ∈ Finset.Icc c n, ((2 ^ i - a) / r) * 2 ^ (n - i))
      ≤ 2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r) := by
  have hpair : n - 1 ≠ n := by omega
  have hsub : Finset.Icc c n ⊆ ({n - 1, n} : Finset ℕ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨h1, h2⟩ := hi
    have h3 : n - 1 ≤ i := le_trans hc h1
    rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc
    (∑ i ∈ Finset.Icc c n, ((2 ^ i - a) / r) * 2 ^ (n - i))
        ≤ ∑ i ∈ ({n - 1, n} : Finset ℕ), ((2 ^ i - a) / r) * 2 ^ (n - i) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro i _ _
          exact Nat.zero_le _
    _ = ((2 ^ (n - 1) - a) / r) * 2 ^ (n - (n - 1)) +
          ((2 ^ n - a) / r) * 2 ^ (n - n) := by
          rw [Finset.sum_pair hpair]
    _ = 2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r) := by
          have h1 : n - (n - 1) = 1 := by omega
          have h2 : n - n = 0 := by omega
          rw [h1, h2, pow_one, pow_zero, mul_one]
          ring

/-- If `n ≥ 1`, `a ≥ 1`, and `r ≥ 2^(n-1)`, the two-term quotient bound is at most eight. -/
theorem orderWidth_tail_le_eight (n a r : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (hr : 2 ^ (n - 1) ≤ r) :
    2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r) ≤ 8 := by
  have hfirst : (2 ^ (n - 1) - a) / r = 0 := by
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le (Nat.sub_lt (pow_pos (by norm_num : (0 : ℕ) < 2) (n - 1)) ha) hr
  have hsecond : (2 ^ n - a) / r ≤ 2 := by
    apply Nat.div_le_of_le_mul
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    calc
      2 ^ n - a ≤ 2 ^ n := Nat.sub_le _ _
      _ = 2 * 2 ^ (n - 1) := hpow
      _ ≤ 2 * r := Nat.mul_le_mul_left 2 hr
      _ = r * 2 := by ring
  rw [hfirst]
  omega

/-- If `n ≥ 1`, `1 ≤ a < r`, and `r ≥ 2^(n-1)`, the exceptional count is bounded by the
logarithmic-prefix term plus the two final quotient contributions. -/
theorem exceptionalDoubling_card_le_two_terms (n a r : ℕ)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (har : a < r) (hr : 2 ^ (n - 1) ≤ r) :
    (ExceptionalDoublingScalars n a r).card ≤
      2 ^ (n - Nat.clog 2 a) + 2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r) := by
  have hcount := exceptionalDoubling_count_le n a r hn ha har
  have hc : n - 1 ≤ Nat.clog 2 r := orderWidth_clog_ge n r hn hr
  have htail := tail_sum_le_two_terms n a r (Nat.clog 2 r) hn hc
  calc
    (ExceptionalDoublingScalars n a r).card
        ≤ 2 ^ (n - Nat.clog 2 a) +
            ∑ i ∈ Finset.Icc (Nat.clog 2 r) n, ((2 ^ i - a) / r) * 2 ^ (n - i) :=
          hcount
    _ ≤ 2 ^ (n - Nat.clog 2 a) +
          (2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r)) :=
          Nat.add_le_add_left htail _
    _ = 2 ^ (n - Nat.clog 2 a) + 2 * ((2 ^ (n - 1) - a) / r) + ((2 ^ n - a) / r) := by
          ring

/-- If `n ≥ 1`, `1 ≤ a < r`, and `r ≥ 2^(n-1)`, there are at most `2^(n - Nat.clog 2 a) + 8`
exceptional strings. -/
theorem exceptionalDoubling_card_le_eight (n a r : ℕ)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (har : a < r) (hr : 2 ^ (n - 1) ≤ r) :
    (ExceptionalDoublingScalars n a r).card ≤ 2 ^ (n - Nat.clog 2 a) + 8 := by
  have h2 := exceptionalDoubling_card_le_two_terms n a r hn ha har hr
  have h8 := orderWidth_tail_le_eight n a r hn ha hr
  omega

end Qatlib.Foundations.FiniteCounts.ExceptionalBits
