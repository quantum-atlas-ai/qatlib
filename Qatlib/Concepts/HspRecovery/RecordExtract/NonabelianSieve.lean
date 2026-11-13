/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianSieveDefs
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe

/-!
# Dihedral sieve descent and sorting bounds

This module proves binary reconstruction, sorting and pairing identities, and probability
formulas for repeated dihedral sieve trials. For an oracle hiding a reflection, `slopeDescent`
assigns zero mass to incorrect slopes and its failure mass is bounded by `descentFailureBound`.

The combined result `clause16` packages descent correctness with record counts and elementary
sorting time and space estimates. See [Kuperberg2005] for the mathematical background.

## Main statements

* `slopeOfBits_slopeBit`: reconstruct a slope from its binary digits.
* `descent_wrong_zero`: incorrect slopes have zero output mass.
* `descent_fail_bound`: bound the failure mass of recursive descent.
* `clause16`: collect the descent and resource statements.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000

noncomputable section

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped Classical BigOperators ENNReal

/-- A natural number below `2 ^ k` equals the weighted sum of its first `k` binary digits. -/
theorem sum_bits_eq (x k : ℕ) (h : x < 2 ^ k) :
    (∑ i : Fin k, if x / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0) = x := by
  induction k generalizing x with
  | zero =>
    have hx : x = 0 := by omega
    subst hx
    simp
  | succ k ih =>
    have hx2 : x / 2 < 2 ^ k := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow] at h
      omega
    have hsum := ih (x / 2) hx2
    have hstep (i : Fin k) : x / 2 ^ ((i : ℕ) + 1) % 2 = 1 ↔ x / 2 / 2 ^ (i : ℕ) % 2 = 1 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    have hterm (i : Fin k) :
        (if x / 2 ^ ((i : ℕ) + 1) % 2 = 1 then (2 ^ ((i : ℕ) + 1) : ℕ) else 0) =
          2 * (if x / 2 / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0) := by
      by_cases hc : x / 2 / 2 ^ (i : ℕ) % 2 = 1
      · have hci : x / 2 ^ ((i : ℕ) + 1) % 2 = 1 := (hstep i).mpr hc
        rw [if_pos hci, if_pos hc, pow_succ]
        ring
      · have hci : ¬ x / 2 ^ ((i : ℕ) + 1) % 2 = 1 := fun hh => hc ((hstep i).mp hh)
        rw [if_neg hci, if_neg hc, mul_zero]
    have htail : (∑ i : Fin k,
        if x / 2 ^ ((i : ℕ) + 1) % 2 = 1 then (2 ^ ((i : ℕ) + 1) : ℕ) else 0) =
          2 * ∑ i : Fin k, if x / 2 / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0 := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    have hlow : (if x / 2 ^ 0 % 2 = 1 then (2 ^ 0 : ℕ) else 0) = x % 2 := by
      have hdiv : x / 2 ^ 0 = x := by simp
      rw [hdiv]
      by_cases hb : x % 2 = 1
      · simp [hb]
      · rw [if_neg hb]
        have hm := Nat.mod_two_eq_zero_or_one x
        omega
    calc (∑ i : Fin (k + 1), if x / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0)
        = (if x / 2 ^ 0 % 2 = 1 then (2 ^ 0 : ℕ) else 0) +
            ∑ i : Fin k, if x / 2 ^ ((i : ℕ) + 1) % 2 = 1 then (2 ^ ((i : ℕ) + 1) : ℕ) else 0 :=
          Fin.sum_univ_succ _
      _ = x % 2 + 2 * (x / 2) := by rw [hlow, htail, hsum]
      _ = x := by omega

/-- Reconstructing a modular slope from its binary digits returns the original slope. -/
theorem slopeOfBits_slopeBit (n : ℕ) (s : ZMod (2 ^ n)) :
    slopeOfBits n (slopeBit n s) = s := by
  have hv : s.val < 2 ^ n := ZMod.val_lt s
  have hsum := sum_bits_eq s.val n hv
  have h : slopeOfBits n (slopeBit n s) =
      ((∑ i : Fin n, if s.val / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0 : ℕ) :
        ZMod (2 ^ n)) := by
    unfold slopeOfBits slopeBit
    simp
  rw [h, hsum]
  exact ZMod.natCast_zmod_val s

/-- Split a binary weighted sum into its least significant bit and twice the shifted sum. -/
theorem sum_bits_shift (b : ℕ → Bool) (n : ℕ) :
    (∑ j : Fin (n + 1), if b j then (2 ^ (j : ℕ) : ℕ) else 0) =
      (if b 0 then (1 : ℕ) else 0) +
        2 * ∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0 := by
  have hterm (j : Fin n) :
      (if b j.succ then (2 ^ (j.succ : ℕ) : ℕ) else 0) =
        2 * (if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0) := by
    by_cases hb : b (j + 1) <;> simp [hb, pow_succ, Nat.mul_comm]
  rw [Fin.sum_univ_succ]
  show (if b 0 then (1 : ℕ) else 0) + ∑ j : Fin n,
      (if b j.succ then (2 ^ (j.succ : ℕ) : ℕ) else 0) = _
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]

/-- A weighted sum of `n` Boolean digits is strictly less than `2 ^ n`. -/
theorem sum_bits_lt (n : ℕ) (b : ℕ → Bool) :
    (∑ j : Fin n, if b j then (2 ^ (j : ℕ) : ℕ) else 0) < 2 ^ n := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have hT : (∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0) < 2 ^ n :=
      ih (fun j => b (j + 1))
    rw [sum_bits_shift b n, pow_succ]
    by_cases hb : b 0 <;> simp [hb] <;> omega

/-- Extracting bit `i < n` from a weighted sum of Boolean digits returns the digit at `i`. -/
theorem sum_bits_bit (n i : ℕ) (b : ℕ → Bool) (hi : i < n) :
    (∑ j : Fin n, if b j then (2 ^ (j : ℕ) : ℕ) else 0) / 2 ^ i % 2 =
      if b i then (1 : ℕ) else 0 := by
  induction n generalizing i b with
  | zero => omega
  | succ n ih =>
    rw [sum_bits_shift b n]
    rcases i with _ | i
    · by_cases hb : b 0 <;> simp [hb]
      all_goals omega
    · have hT : (∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0) / 2 ^ i % 2 =
          if b (i + 1) then (1 : ℕ) else 0 := ih i (fun j => b (j + 1)) (by omega)
      have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
      have hhalf : ((if b 0 then (1 : ℕ) else 0) + 2 *
          (∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0)) / 2 =
          ∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0 := by
        by_cases hb : b 0 <;> simp [hb] <;> omega
      have hdiv : ((if b 0 then (1 : ℕ) else 0) + 2 *
          (∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0)) / (2 * 2 ^ i) =
          (∑ j : Fin n, if b (j + 1) then (2 ^ (j : ℕ) : ℕ) else 0) / 2 ^ i := by
        rw [← Nat.div_div_eq_div_mul, hhalf]
      rw [hpow, hdiv, hT]

/-- The first `n` digits of a slope reconstructed from `b` agree with `b`. -/
theorem slopeBit_slopeOfBits (n : ℕ) (b : ℕ → Bool) (i : ℕ) (hi : i < n) :
    slopeBit n (slopeOfBits n b) i = b i := by
  have hS : (∑ j : Fin n, if b j then (2 ^ (j : ℕ) : ℕ) else 0) < 2 ^ n := sum_bits_lt n b
  have hval : (slopeOfBits n b).val = (∑ j : Fin n, if b j then (2 ^ (j : ℕ) : ℕ) else 0) := by
    unfold slopeOfBits
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hS]
  have hbit := sum_bits_bit n i b hi
  unfold slopeBit
  rw [hval]
  by_cases hb : b i <;> simp [hb, decide_eq_true_eq] at hbit ⊢ <;> exact hbit

/-- Insertion by key produces a permutation of the list with the inserted element prepended. -/
theorem insertByKey_perm {α : Type} (key : α → ℕ) (a : α) (L : List α) :
    List.Perm (insertByKey key a L) (a :: L) := by
  induction L with
  | nil => simp [insertByKey]
  | cons b rest ih =>
    unfold insertByKey
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)

/-- Insertion by key increases the list length by one. -/
theorem insertByKey_length {α : Type} (key : α → ℕ) (a : α) (L : List α) :
    (insertByKey key a L).length = L.length + 1 := by
  induction L with
  | nil => rfl
  | cons b rest ih =>
    unfold insertByKey
    split_ifs <;> simp [ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Insertion by key preserves nondecreasing key order. -/
theorem insertByKey_sorted {α : Type} (key : α → ℕ) (a : α) (L : List α)
    (h : sortedByKey key L) : sortedByKey key (insertByKey key a L) := by
  induction L with
  | nil => simp [insertByKey, sortedByKey]
  | cons b rest ih =>
    have hrest : sortedByKey key rest := by
      cases rest with
      | nil => trivial
      | cons c rest' => exact h.2
    unfold insertByKey
    split_ifs with hab
    · exact ⟨hab, h⟩
    · cases rest with
      | nil =>
        simp only [insertByKey]
        exact ⟨le_of_lt (lt_of_not_ge hab), trivial⟩
      | cons c rest' =>
        simp only [insertByKey]
        split_ifs with hac
        · exact ⟨le_of_lt (lt_of_not_ge hab), hac, h.2⟩
        · exact ⟨h.1, by simpa [insertByKey, hac] using ih hrest⟩

/-- Sorting records preserves their multiset of entries and their length. -/
theorem sortRecords_perm {α : Type} (key : α → ℕ) (L : List α) :
    List.Perm (sortRecords key L) L ∧ (sortRecords key L).length = L.length := by
  induction L with
  | nil => exact ⟨List.Perm.nil, rfl⟩
  | cons r rest ih =>
    unfold sortRecords
    have hlen : (insertByKey key r (sortRecords key rest)).length = (r :: rest).length := by
      rw [insertByKey_length, ih.2]
      rfl
    exact ⟨(insertByKey_perm key r (sortRecords key rest)).trans (ih.1.cons r), hlen⟩

/-- Sorting records yields a list in nondecreasing key order. -/
theorem sortRecords_sorted {α : Type} (key : α → ℕ) (L : List α) :
    sortedByKey key (sortRecords key L) := by
  induction L with
  | nil => simp [sortRecords, sortedByKey]
  | cons r rest ih =>
    unfold sortRecords
    exact insertByKey_sorted key r (sortRecords key rest) ih

/-- The insertion comparison count is at most the input list length. -/
theorem insertCompareCount_le {α : Type} (key : α → ℕ) (a : α) (L : List α) :
    insertCompareCount key a L ≤ L.length := by
  induction L with
  | nil => simp [insertCompareCount]
  | cons b rest ih =>
    unfold insertCompareCount
    split_ifs <;> simp only [List.length_cons] <;> omega

/-- The sorting comparison count is at most the square of the list length. -/
theorem sortCompareCount_le {α : Type} (key : α → ℕ) (L : List α) :
    sortCompareCount key L ≤ L.length * L.length := by
  induction L with
  | nil => simp [sortCompareCount]
  | cons r rest ih =>
    unfold sortCompareCount
    have hlen : (sortRecords key rest).length = rest.length := (sortRecords_perm key rest).2
    have h1 : insertCompareCount key r (sortRecords key rest) ≤ rest.length := by
      rw [← hlen]
      exact insertCompareCount_le key r (sortRecords key rest)
    have h2 : rest.length + rest.length * rest.length ≤
        (rest.length + 1) * (rest.length + 1) := by
      have heq : (rest.length + 1) * (rest.length + 1) =
          rest.length * rest.length + (rest.length + rest.length + 1) := by ring
      rw [heq]
      have hle : rest.length ≤ rest.length + rest.length + 1 := by omega
      have hadd := Nat.add_le_add_left hle (rest.length * rest.length)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd
    have hsum := Nat.add_le_add h1 ih
    exact le_trans hsum h2

/-- Every pair returned by `sortedPairs` has equal keys. -/
theorem sortedPairs_keys {α : Type} (key : α → ℕ) (L : List α) (p : α × α)
    (hp : p ∈ sortedPairs key L) : key p.1 = key p.2 := by
  fun_induction sortedPairs key L
  case case1 h ih =>
    rcases List.mem_cons.mp hp with heq | hin
    · rw [heq]
      exact h
    · exact ih hin
  case case2 h ih =>
    exact ih hp
  case case3 =>
    simp at hp

/-- The number of entries used by `sortedPairs` is at most the input length. -/
theorem sortedPairs_len_le {α : Type} (key : α → ℕ) (L : List α) :
    2 * (sortedPairs key L).length ≤ L.length := by
  fun_induction sortedPairs key L
  case case1 h ih =>
    simp only [List.length_cons, List.length_nil] at ih ⊢
    omega
  case case2 h ih =>
    simp only [List.length_cons] at ih ⊢
    omega
  case case3 =>
    simp

/-- The tail of a list sorted by key is sorted by key. -/
theorem sortedByKey_tail {α : Type} (key : α → ℕ) (a : α) (L : List α)
    (h : sortedByKey key (a :: L)) : sortedByKey key L := by
  cases L with
  | nil => trivial
  | cons b rest => exact h.2

/-- The key of the head of a sorted list is at most the key of every tail entry. -/
theorem sortedByKey_mem_le {α : Type} (key : α → ℕ) :
    ∀ (c : α) (L : List α), sortedByKey key (c :: L) → ∀ x ∈ L, key c ≤ key x := by
  intro c L
  induction L generalizing c with
  | nil => intro h x hx; simp at hx
  | cons b rest ih =>
    intro h x hx
    have hab : key c ≤ key b := h.1
    have hrest : sortedByKey key (b :: rest) := h.2
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]
      exact hab
    · exact le_trans hab (ih b hrest x hx)

/-- In a sorted list, the number of pairs with key `u` is half the number of entries with that
key, rounded down. -/
theorem sortedPairs_count {α : Type} (key : α → ℕ) (u : ℕ) :
    ∀ (L : List α), sortedByKey key L →
      (sortedPairs key L).countP (fun p => decide (key p.1 = u)) =
        (L.countP (fun r => decide (key r = u))) / 2 := by
  have hall : ∀ n (L : List α), L.length = n → sortedByKey key L →
      (sortedPairs key L).countP (fun p => decide (key p.1 = u)) =
        (L.countP (fun r => decide (key r = u))) / 2 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro L hlen hs
      cases L with
      | nil => simp [sortedPairs]
      | cons a L' =>
        cases L' with
        | nil =>
          by_cases hu : key a = u <;> simp [sortedPairs, List.countP_cons, hu]
        | cons b rest =>
          rw [List.length_cons, List.length_cons] at hlen
          have hlen_rest : rest.length < n := by omega
          have hlen_brest : (b :: rest).length < n := by simp only [List.length_cons]; omega
          have hs_brest : sortedByKey key (b :: rest) := hs.2
          have hs_rest : sortedByKey key rest := sortedByKey_tail key b rest hs_brest
          have ih_rest := ih rest.length hlen_rest rest rfl hs_rest
          have ih_brest := ih (b :: rest).length hlen_brest (b :: rest) rfl hs_brest
          by_cases hab : key a = key b
          · have hpair : sortedPairs key (a :: b :: rest) = (a, b) :: sortedPairs key rest := by
              simp [sortedPairs, hab]
            rw [hpair]
            have hco : ((a, b) :: sortedPairs key rest).countP
                (fun p => decide (key p.1 = u)) =
                (sortedPairs key rest).countP (fun p => decide (key p.1 = u)) +
                  (if key a = u then 1 else 0) := by
              by_cases hu : key a = u <;> simp [List.countP_cons, hu]
            rw [hco, ih_rest]
            have hcl : (a :: b :: rest).countP (fun r => decide (key r = u)) =
                rest.countP (fun r => decide (key r = u)) +
                  (if decide (key b = u) = true then 1 else 0) +
                  (if decide (key a = u) = true then 1 else 0) := by
              rw [List.countP_cons, List.countP_cons]
            rw [hcl, hab]
            by_cases hu : key a = u <;> simp [hu] <;> omega
          · have hpair : sortedPairs key (a :: b :: rest) = sortedPairs key (b :: rest) := by
              simp [sortedPairs, hab]
            rw [hpair, ih_brest]
            have hlt : key a < key b := lt_of_le_of_ne hs.1 hab
            have hmem : ∀ x ∈ b :: rest, key a < key x := by
              intro x hx
              have hbx : key b ≤ key x := by
                rcases List.mem_cons.mp hx with hx | hx
                · subst hx
                  exact le_rfl
                · exact sortedByKey_mem_le key b rest hs_brest x hx
              exact lt_of_lt_of_le hlt hbx
            have hcl : (a :: b :: rest).countP (fun r => decide (key r = u)) =
                (b :: rest).countP (fun r => decide (key r = u)) +
                  (if key a = u then 1 else 0) := by
              by_cases hu : key a = u <;> simp [List.countP_cons, hu]
            rw [hcl]
            by_cases hu : key a = u
            · have hne : ∀ x ∈ b :: rest, ¬ (key x = u) := by
                intro x hx
                have hlt2 := hmem x hx
                rw [hu] at hlt2
                exact ne_of_gt hlt2
              have hz : (b :: rest).countP (fun r => decide (key r = u)) = 0 := by
                rw [List.countP_eq_zero]
                intro x hx
                simp [hne x hx]
              rw [if_pos hu, hz]
            · rw [if_neg hu, Nat.add_zero]
  intro L
  exact hall L.length L rfl

/-- Summing the counts of all possible keys recovers the list length when every key is below
`R`. -/
theorem sum_class_count {α : Type} (key : α → ℕ) (R : ℕ)
    (hk : ∀ a, key a < R) (L : List α) :
    (∑ u ∈ Finset.range R, L.countP (fun a => decide (key a = u))) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hcons : ∀ u : ℕ,
        (a :: L).countP (fun x => decide (key x = u)) =
          L.countP (fun x => decide (key x = u)) + (if decide (key a = u) = true then 1 else 0) := by
      intro u
      rw [List.countP_cons]
    simp_rw [hcons, decide_eq_true_eq]
    rw [Finset.sum_add_distrib, ih]
    have hone : (∑ u ∈ Finset.range R, (if key a = u then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_boole]
      have hmem : key a ∈ Finset.range R := Finset.mem_range.mpr (hk a)
      have hfeq : (Finset.range R).filter (fun u => key a = u) = {key a} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro h
          exact h.2.symm
        · intro h
          subst h
          exact ⟨hk a, rfl⟩
      rw [hfeq]
      simp
    simpa [Nat.add_comm, Nat.add_left_comm] using congrArg (fun z => z + L.length) hone

/-- Window agreement is equivalent to equality of the corresponding window keys. -/
theorem windowAgree_iff_windowKey (n w t : ℕ) (k ℓ : ZMod (2 ^ n)) :
    windowAgree n w t k ℓ ↔ windowKey n w t k = windowKey n w t ℓ :=
  Iff.rfl

/-- For each window key, sieve pairing produces half the number of entries with that key,
rounded down. -/
theorem sievePairWith_count (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (L : List α) :
    ∀ u : ℕ,
      (sievePairWith n label w t L).countP
          (fun p => decide (windowKey n w t (label p.1) = u)) =
        (L.countP (fun r => decide (windowKey n w t (label r) = u))) / 2 := by
  fun_induction sievePairWith n label w t L
  · intro u
    simp
  · rename_i r rest h ih
    intro u
    by_cases hu : windowKey n w t (label r) = u
    · have hc : rest.countP (fun a => decide (windowKey n w t (label a) = u)) = 0 := by
        apply List.countP_eq_zero.2
        intro a ha
        have hn := List.find?_eq_none.1 h a ha
        simp only [decide_eq_true_eq] at hn ⊢
        exact fun he => hn (hu.trans he.symm)
      rw [List.countP_cons, ih u, hc]
      simp [hu]
    · simpa [List.countP_cons, hu] using ih u
  · intro u
    rename_i r rest r' h ih
    have hm : r' ∈ rest := List.mem_of_find?_eq_some h
    have he : windowKey n w t (label r) = windowKey n w t (label r') := by
      simpa only [decide_eq_true_eq, windowAgree, windowKey] using List.find?_some h
    by_cases hu : windowKey n w t (label r) = u
    · have hu' : windowKey n w t (label r') = u := he.symm.trans hu
      have hpos : 0 < rest.countP (fun a => decide (windowKey n w t (label a) = u)) :=
        List.countP_pos_iff.2 ⟨r', hm, by simp [hu']⟩
      rw [List.countP_cons, List.countP_cons, ih u, List.countP_erase]
      simp only [hu, hu', decide_true, if_true, hm, and_self]
      omega
    · have hu' : windowKey n w t (label r') ≠ u := fun he' => hu (he.trans he')
      rw [List.countP_cons, List.countP_cons, ih u, List.countP_erase]
      simp [hu, hu', hm]

/-- Greedy sieve pairing and pairing after sorting by window key produce the same number of
pairs. -/
theorem sievePairWith_sorted_count (n w t : ℕ) (α : Type) [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (L : List α) :
    (sievePairWith n label w t L).length =
      (sortedPairs (fun r => windowKey n w t (label r))
        (sortRecords (fun r => windowKey n w t (label r)) L)).length := by
  have keyhk : ∀ a : α, windowKey n w t (label a) < 2 ^ w := fun a =>
    Nat.mod_lt _ (by positivity)
  have hsumP := sum_class_count (fun p : α × α => windowKey n w t (label p.1)) (2 ^ w)
    (fun p => keyhk p.1) (sievePairWith n label w t L)
  have hsumS := sum_class_count (fun p : α × α => windowKey n w t (label p.1)) (2 ^ w)
    (fun p => keyhk p.1)
      (sortedPairs (fun r => windowKey n w t (label r))
        (sortRecords (fun r => windowKey n w t (label r)) L))
  rw [← hsumP, ← hsumS]
  apply Finset.sum_congr rfl
  intro u _
  have h1 := sievePairWith_count n label w t L u
  have h2 := sortedPairs_count (fun r => windowKey n w t (label r)) u
    (sortRecords (fun r => windowKey n w t (label r)) L)
    (sortRecords_sorted (fun r => windowKey n w t (label r)) L)
  have h3 : (sortRecords (fun r => windowKey n w t (label r)) L).countP
        (fun r => decide (windowKey n w t (label r) = u)) =
      L.countP (fun r => decide (windowKey n w t (label r) = u)) :=
    (sortRecords_perm (fun r => windowKey n w t (label r)) L).1.countP_eq _
  rw [h1, h2, h3]

/-- Every level record budget is at least one. -/
theorem levelRecords_pos (k : ℕ) : 1 ≤ levelRecords k := by
  have h : 0 < levelRecords k := by unfold levelRecords; positivity
  omega

/-- Every level trial count is at least one. -/
theorem levelTrials_pos (k : ℕ) : 1 ≤ levelTrials k := by
  have h : 0 < levelTrials k := by unfold levelTrials sourceParityTrials; positivity
  omega

/-- The sorting comparison count times `k + 1` is bounded by `sortBitTime`. -/
theorem sortBitTime_bound {α : Type} (key : α → ℕ) (L : List α) (k : ℕ) :
    sortCompareCount key L * (k + 1) ≤ sortBitTime k L.length := by
  have h := sortCompareCount_le key L
  have h2 := Nat.mul_le_mul_right (k + 1) h
  unfold sortBitTime
  exact le_trans h2 (Nat.le_add_right _ _)

/-- The total descent sorting time is bounded by the sum of twice the squared level record
budgets times `k + 1`. -/
theorem descentBitTime_bound (n : ℕ) :
    descentBitTime n ≤ ∑ k ∈ Finset.Icc 1 n, 2 * (levelTrials k * levelRecords k) ^ 2 * (k + 1) := by
  unfold descentBitTime
  apply Finset.sum_le_sum
  intro k hk
  have hR1 : 1 ≤ levelTrials k * levelRecords k := by
    have := Nat.mul_le_mul (levelTrials_pos k) (levelRecords_pos k)
    simpa using this
  have hR : levelTrials k * levelRecords k ≤ (levelTrials k * levelRecords k) * (levelTrials k * levelRecords k) :=
    le_trans (le_of_eq (one_mul _).symm) (Nat.mul_le_mul_right _ hR1)
  have hR2 : (levelTrials k * levelRecords k) ^ 2 =
      (levelTrials k * levelRecords k) * (levelTrials k * levelRecords k) :=
    pow_two _
  have hmul : levelTrials k * levelRecords k * (k + 1) ≤
      (levelTrials k * levelRecords k) * (levelTrials k * levelRecords k) * (k + 1) :=
    Nat.mul_le_mul_right (k + 1) hR
  unfold sortBitTime
  rw [hR2]
  calc levelTrials k * levelRecords k * (levelTrials k * levelRecords k) * (k + 1) +
        levelTrials k * levelRecords k * (k + 1) ≤
      levelTrials k * levelRecords k * (levelTrials k * levelRecords k) * (k + 1) +
        levelTrials k * levelRecords k * (levelTrials k * levelRecords k) * (k + 1) :=
        Nat.add_le_add_left hmul _
    _ = 2 * (levelTrials k * levelRecords k * (levelTrials k * levelRecords k)) * (k + 1) := by
          ring

/-- The workspace budget at any level from one through `n` is bounded by `descentSpace n`. -/
theorem descentSpace_ge (n k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
    sortSpace k (levelTrials k * levelRecords k) ≤ descentSpace n := by
  unfold descentSpace
  exact Finset.le_sup (f := fun k => sortSpace k (levelTrials k * levelRecords k)) hk

/-- The peak descent workspace is bounded by the sum of all level workspace budgets. -/
theorem descentSpace_le (n : ℕ) :
    descentSpace n ≤ ∑ k ∈ Finset.Icc 1 n, levelTrials k * levelRecords k * k := by
  unfold descentSpace sortSpace
  apply Finset.sup_le
  intro k hk
  exact Finset.single_le_sum (f := fun i => levelTrials i * levelRecords i * i)
    (fun i _ => Nat.zero_le _) hk

/-- The level width at `n + 1` is the ceiling of `sqrt n`. -/
theorem levelWidth_succ (n : ℕ) : levelWidth (n + 1) = Nat.ceil (Real.sqrt (n : ℝ)) := by
  unfold levelWidth
  push_cast
  ring_nf

/-- The total descent record count equals `sourcePowerTwoQueryBudget`. -/
theorem descentRecords_eq (n : ℕ) : descentRecords n = sourcePowerTwoQueryBudget n := by
  unfold descentRecords
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    rw [sourcePowerTwoQueryBudget]
    have h1 : levelTrials (n + 1) = sourceParityTrials (n + 1) := rfl
    have h2 : levelRecords (n + 1) = 24 * 2 ^ (3 * Nat.ceil (Real.sqrt (n : ℝ))) := by
      unfold levelRecords
      rw [levelWidth_succ]
    rw [h1, h2]
    ac_rfl

/-- Failure after `r + 1` trials is the product of one-trial failure mass and failure after `r`
trials. -/
theorem firstAnswer_succ_none (r : ℕ) (p : PMF (Option Bool)) :
    (firstAnswer (r + 1) p) none = p none * (firstAnswer r p) none := by
  have hbind : firstAnswer (r + 1) p =
      p.bind fun o => match o with
        | some b => PMF.pure (some b)
        | none => firstAnswer r p := rfl
  rw [hbind, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hzero : ∑ x : Bool, p (some x) * (PMF.pure (some x)) none = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [PMF.pure_apply_of_ne _ _ (show (none : Option Bool) ≠ some b by simp)]
    exact mul_zero _
  rw [hzero, add_zero]

/-- The failure mass after `r` first-answer trials is the `r`th power of the single-trial
failure mass. -/
theorem firstAnswer_none (r : ℕ) (p : PMF (Option Bool)) :
    (firstAnswer r p) none = p none ^ r := by
  induction r with
  | zero =>
    show (PMF.pure none : PMF (Option Bool)) none = p none ^ 0
    rw [PMF.pure_apply_self none, pow_zero]
  | succ r ih =>
    rw [firstAnswer_succ_none, ih, pow_succ']

/-- The mass of an answer after `r + 1` trials is its one-trial mass plus the one-trial failure
mass times its mass after `r` trials. -/
theorem firstAnswer_succ_some (r : ℕ) (p : PMF (Option Bool)) (b : Bool) :
    (firstAnswer (r + 1) p) (some b) =
      p (some b) + p none * (firstAnswer r p) (some b) := by
  have hbind : firstAnswer (r + 1) p =
      p.bind fun o => match o with
        | some b => PMF.pure (some b)
        | none => firstAnswer r p := rfl
  rw [hbind, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hsum : ∑ x : Bool, p (some x) * (PMF.pure (some x)) (some b) = p (some b) := by
    rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)]
    · rw [PMF.pure_apply_self (some b), mul_one]
    · intro x _ hxb
      have hne : (some b : Option Bool) ≠ some x := by
        intro hh
        simp at hh
        exact hxb hh.symm
      rw [PMF.pure_apply_of_ne _ _ hne]
      exact mul_zero _
  rw [hsum, add_comm]

/-- Repeating a law with zero mass at a given answer preserves zero mass at that answer. -/
theorem firstAnswer_wrong_zero (r : ℕ) (p : PMF (Option Bool)) (b : Bool)
    (hb : p (some b) = 0) : (firstAnswer r p) (some b) = 0 := by
  induction r with
  | zero =>
    show (PMF.pure none : PMF (Option Bool)) (some b) = 0
    rw [PMF.pure_apply_of_ne _ _ (show (some b : Option Bool) ≠ none by simp)]
  | succ r ih =>
    rw [firstAnswer_succ_some, hb, zero_add, ih, mul_zero]

/-- For a fixed parity bit, `parityLift` is injective. -/
theorem parityLift_injective (n : ℕ) (b : Bool) :
    Function.Injective (parityLift n b) := by
  intro t t' he
  apply ZMod.val_injective
  have h := congrArg ZMod.val he
  rw [parityLift_val, parityLift_val] at h
  omega

/-- For a reflection-hiding oracle, repeated level trials assign zero mass to the incorrect
parity bit. -/
theorem levelRun_wrong_zero {k : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ k) → S) (s : ZMod (2 ^ k))
    (hf : DihedralReflectionHides (2 ^ k) f s) (b : Bool)
    (hb : b ≠ decide (s.val % 2 = 1)) : (levelRunTrials k f) (some b) = 0 := by
  have hbridge : levelRun k f = (dihedralSieveRun k (levelWidth k) s).1 :=
    dihedralSieveBridge k (levelWidth k) S f s hf
  have hwrong : (dihedralSieveRun k (levelWidth k) s).1 (some b) = 0 :=
    dihedralSieveWrongAnswerZero k (levelWidth k) s b hb
  unfold levelRunTrials
  rw [hbridge]
  exact firstAnswer_wrong_zero (levelTrials k) _ b hwrong

/-- At exponent zero, slope descent deterministically returns the zero residue. -/
theorem slopeDescent_zero {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ 0) → S) :
    slopeDescent 0 S f = (PMF.pure (some 0) : PMF (Option (ZMod (2 ^ 0)))) := rfl

/-- At exponent one, slope descent maps the repeated parity answer to its residue modulo two. -/
theorem slopeDescent_one {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ 1) → S) :
    slopeDescent 1 S f =
      (levelRunTrials 1 f).map fun o => o.map fun b => (if b then (1 : ZMod 2) else 0) := rfl

/-- At exponent `k + 2`, slope descent first obtains a parity bit, recursively solves the
restricted oracle, and lifts the result. -/
theorem slopeDescent_ss {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (k : ℕ) (f : DihedralReg (2 ^ (k + 2)) → S) :
    slopeDescent (k + 2) S f =
      (levelRunTrials (k + 2) f).bind fun o =>
        match o with
        | none => PMF.pure none
        | some b =>
          (slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b)).map fun o =>
            o.map fun t => parityLift (k + 1) b t := rfl

/-- Mapping an optional output through `Option.map` preserves its failure mass. -/
theorem optionMap_none {α β : Type} [Fintype α] (g : α → β) (p : PMF (Option α)) :
    (p.map fun o => o.map g) none = p none := by
  have hmap : (p.map fun o => o.map g) = p.bind (fun o => PMF.pure (o.map g)) := rfl
  rw [hmap, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hzero : ∑ x : α, p (some x) * (PMF.pure (Option.map g (some x))) none = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [PMF.pure_apply_of_ne _ _
      (show (none : Option β) ≠ Option.map g (some a) by simp)]
    exact mul_zero _
  have hone : (PMF.pure ((none : Option α).map g)) none = 1 := by
    show (PMF.pure none : PMF (Option β)) none = 1
    exact PMF.pure_apply_self none
  rw [hone, mul_one, hzero, add_zero]

/-- An optional mapped law has zero mass at `some y` when every supported input answer maps away
from `y`. -/
theorem optionMap_some_zero {α β : Type} [Fintype α] (g : α → β) (p : PMF (Option α))
    (y : β) (h : ∀ a, p (some a) ≠ 0 → g a ≠ y) :
    (p.map fun o => o.map g) (some y) = 0 := by
  have hmap : (p.map fun o => o.map g) = p.bind (fun o => PMF.pure (o.map g)) := rfl
  rw [hmap, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hzero : ∑ x : α, p (some x) * (PMF.pure (Option.map g (some x))) (some y) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hpa : p (some a) = 0
    · rw [hpa, zero_mul]
    · have hne : (some y : Option β) ≠ Option.map g (some a) := by
        intro hh
        have hg : g a = y := by simpa using (Option.some.inj hh).symm
        exact h a hpa hg
      rw [PMF.pure_apply_of_ne _ _ hne, mul_zero]
  have hnone : (PMF.pure ((none : Option α).map g)) (some y) = 0 := by
    show (PMF.pure none : PMF (Option β)) (some y) = 0
    rw [PMF.pure_apply_of_ne _ _ (show (some y : Option β) ≠ none by simp)]
  rw [hnone, mul_zero, hzero, add_zero]

/-- A residue modulo two is determined by whether its canonical representative is odd. -/
theorem parityBit_one (s : ZMod 2) :
    (if decide (s.val % 2 = 1) then (1 : ZMod 2) else 0) = s := by
  have hv : s.val < 2 := ZMod.val_lt s
  have hmod : s.val % 2 = s.val := Nat.mod_eq_of_lt hv
  rw [hmod]
  by_cases h : s.val = 1
  · rw [h]
    simp
    rw [show s = ((s.val : ℕ) : ZMod 2) from (ZMod.natCast_zmod_val s).symm, h, Nat.cast_one]
  · have h0 : s.val = 0 := by omega
    rw [h0]
    simp
    rw [show s = ((s.val : ℕ) : ZMod 2) from (ZMod.natCast_zmod_val s).symm, h0, Nat.cast_zero]

/-- For an oracle hiding slope `s`, recursive slope descent assigns zero mass to every different
slope. -/
theorem descent_wrong_zero :
    ∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
    DihedralReflectionHides (2 ^ n) f s →
    ∀ s' : ZMod (2 ^ n), s' ≠ s → slopeDescent n S f (some s') = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro S _ _ _ f s hf s' hs'
    cases n with
    | zero =>
      have h1 : s' = s := by
        apply ZMod.val_injective
        have h2 := ZMod.val_lt s'
        have h3 := ZMod.val_lt s
        omega
      exact absurd h1 hs'
    | succ n1 =>
      cases n1 with
      | zero =>
        rw [slopeDescent_one]
        refine optionMap_some_zero _ _ s' ?_
        intro b hpb
        show (if b then (1 : ZMod 2) else 0) ≠ s'
        have hb : b = decide (s.val % 2 = 1) := by
          by_contra hne
          exact hpb (levelRun_wrong_zero f s hf b hne)
        rw [hb, parityBit_one]
        exact hs'.symm
      | succ k =>
        have hdef : slopeDescent (Nat.succ (Nat.succ k)) S f
            = slopeDescent (k + 2) S f := rfl
        rw [hdef, slopeDescent_ss k f, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
        have hnone : (PMF.pure (none : Option (ZMod (2 ^ (k + 2))))) (some s') = 0 := by
          rw [PMF.pure_apply_of_ne _ _
            (show (some s') ≠ (none : Option (ZMod (2 ^ (k + 2)))) by simp)]
        have hsum : ∑ b : Bool, (levelRunTrials (k + 2) f) (some b) *
            ((slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b)).map fun o =>
              o.map fun t => parityLift (k + 1) b t) (some s') = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          by_cases hb : b = decide (s.val % 2 = 1)
          · subst hb
            have huniq := parityLift_unique (k + 1) s
            obtain ⟨tstar, hlift, hunique⟩ := huniq
            have hres : DihedralReflectionHides (2 ^ (k + 1))
                (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) tstar := by
              apply parityRestriction_hides (k + 1) f (decide (s.val % 2 = 1)) tstar
              rw [hlift]
              exact hf
            have hwrong : ∀ u : ZMod (2 ^ (k + 1)),
                u ≠ tstar → slopeDescent (k + 1) S
                  (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) (some u) = 0 :=
              ih (k + 1) (by omega) S
                (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) tstar hres
            rw [optionMap_some_zero _ _ s' ?_, mul_zero]
            intro t hpt
            show parityLift (k + 1) (decide (s.val % 2 = 1)) t ≠ s'
            by_contra ht
            have htstar : t = tstar := by
              by_contra hne
              exact hpt (hwrong t hne)
            subst htstar
            rw [hlift] at ht
            exact hs' ht.symm
          · rw [levelRun_wrong_zero f s hf b hb, zero_mul]
        rw [hnone, mul_zero, hsum, add_zero]

/-- For an oracle hiding slope `s`, the mass of `some s` is one minus the failure mass. -/
theorem descent_mass (n : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    slopeDescent n S f (some s) = 1 - slopeDescent n S f none := by
  set d := slopeDescent n S f
  have hsum : ∑' x : Option (ZMod (2 ^ n)), d x = 1 := PMF.tsum_coe d
  rw [tsum_fintype, Fintype.sum_option] at hsum
  have hsingle : ∑ x : ZMod (2 ^ n), d (some x) = d (some s) := by
    rw [Finset.sum_eq_single_of_mem s (Finset.mem_univ s)]
    intro x _ hxs
    exact descent_wrong_zero n S f s hf x hxs
  rw [hsingle, add_comm] at hsum
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top hsum

/-- The expectation of a nonnegative extended-real function under a pure law is its value at the
chosen point. -/
theorem pmf_pure_expectation {α : Type} (a : α) (g : α → ℝ≥0∞) :
    ∑' x, (PMF.pure a) x * g x = g a := by
  have hpt : ∀ x, (PMF.pure a) x * g x = if x = a then g x else 0 := by
    intro x
    rw [PMF.pure_apply]
    by_cases hx : x = a <;> simp [hx]
  simp only [hpt]
  rw [tsum_eq_single a]
  · rw [if_pos rfl]
  · intro x hx
    rw [if_neg hx]

/-- Expectation under a bound probability law equals the iterated expectation. -/
theorem pmf_bind_expectation {α β : Type} (p : PMF α) (k : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' y, (p.bind k) y * g y = ∑' x, p x * ∑' y, k x y * g y := by
  have h : ∀ y, (p.bind k) y * g y = ∑' x, p x * (k x y * g y) := by
    intro y
    rw [PMF.bind_apply]
    rw [← ENNReal.tsum_mul_right]
    simp_rw [mul_assoc]
  simp only [h]
  rw [ENNReal.tsum_comm]
  have h2 : ∀ x, ∑' y, p x * (k x y * g y) = p x * ∑' y, k x y * g y :=
    fun x => ENNReal.tsum_mul_left
  simp only [h2]

/-- Expectation under a mapped probability law equals expectation of the composed function. -/
theorem pmf_map_expectation {α β : Type} (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' y, (p.map f) y * g y = ∑' x, p x * g (f x) := by
  have hmap : p.map f = p.bind fun x => PMF.pure (f x) := rfl
  rw [hmap, pmf_bind_expectation]
  simp only [pmf_pure_expectation]

/-- The indicator, valued in `ℝ≥0∞`, that the target element is absent from a list. -/
def missWeight {α : Type} [DecidableEq α] (h : α) : List α → ℝ≥0∞ :=
  fun L => if h ∈ L then 0 else 1

/-- The empty list misses every target, so its miss weight is one. -/
theorem missWeight_nil {α : Type} [DecidableEq α] (h : α) : missWeight h [] = 1 := by
  simp [missWeight]

/-- Prepending the target makes the miss weight zero; otherwise it preserves the tail miss
weight. -/
theorem missWeight_cons {α : Type} [DecidableEq α] (h r : α) (L : List α) :
    missWeight h (r :: L) = if r = h then 0 else missWeight h L := by
  by_cases hr : r = h
  · subst hr
    simp [missWeight]
  · have hne : h ≠ r := fun he => hr he.symm
    by_cases hh : h ∈ L <;> simp [missWeight, List.mem_cons, hr, hne, hh]

/-- Mapping every outcome to `some` gives zero mass to `none`. -/
theorem map_some_none {α : Type} [Fintype α] (p : PMF α) : (p.map some) none = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  rw [if_neg (show (none : Option α) ≠ some a by simp)]

/-- Ideal readout has failure mass zero exactly when the list contains the target label, and one
otherwise. -/
theorem idealReadout_none (n : ℕ) (s : ZMod (2 ^ n)) (L : List (ZMod (2 ^ n))) :
    (idealReadout n s L) none =
      if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 0 else 1 := by
  unfold idealReadout
  by_cases hin : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
  · cases hfind : L.find? (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
    | none =>
      have hno : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∉ L := by
        intro hh
        have h := List.find?_eq_none.1 hfind ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) hh
        simp at h
      exact absurd hin hno
    | some r =>
      show (PMF.map some (parityReadout (dihedralQubitState (2 ^ n) s r)
          (normalized_dihedralQubitState (2 ^ n) s r))) none =
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 0 else 1
      rw [map_some_none, if_pos hin]
  · have hfind : L.find? (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp only [decide_eq_true_eq]
      exact fun heq => hin (heq ▸ hx)
    rw [hfind]
    show (PMF.pure none : PMF (Option Bool)) none =
      if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 0 else 1
    rw [PMF.pure_apply_self none, if_neg hin]

/-- Every residue modulo two equals zero or one. -/
theorem zmod_two_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have hv : r.val < 2 := ZMod.val_lt r
  rw [show r = ((r.val : ℕ) : ZMod 2) from (ZMod.natCast_zmod_val r).symm]
  interval_cases r.val <;> simp

/-- On `ZMod 2`, summing a constant away from one selected point gives that constant. -/
theorem zmod_two_tsum_ite (h : ZMod 2) (s : ℝ≥0∞) :
    ∑' r : ZMod 2, (if r = h then (0 : ℝ≥0∞) else s) = s := by
  rw [tsum_fintype]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext r
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro _; exact zmod_two_cases r
    · intro _; exact Finset.mem_univ r
  rw [huniv, Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide)]
  obtain rfl | rfl := zmod_two_cases h <;> simp

set_option backward.isDefEq.respectTransparency true in

/-- With zero fresh records modulo two, the expected miss weight is one. -/
theorem freshMiss_zero (h : ZMod 2) :
    ∑' L : List (ZMod 2), (idealFreshRecords 1 0) L * missWeight h L = 1 := by
  have hz : idealFreshRecords 1 0 = (PMF.pure [] : PMF (List (ZMod 2))) := rfl
  rw [hz, pmf_pure_expectation, missWeight_nil]

set_option backward.isDefEq.respectTransparency true in

/-- Adding one uniform record modulo two multiplies the expected miss weight by the reciprocal
of the group cardinality. -/
theorem freshMiss_succ (h : ZMod 2) (i : ℕ) :
    ∑' L : List (ZMod 2), (idealFreshRecords 1 (i + 1)) L * missWeight h L =
      ((Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹) *
        (∑' L : List (ZMod 2), (idealFreshRecords 1 i) L * missWeight h L) := by
  have hstep : idealFreshRecords 1 (i + 1) =
      (PMF.uniformOfFintype' (ZMod 2)).bind fun r =>
        (idealFreshRecords 1 i).map fun L => r :: L := rfl
  rw [hstep, pmf_bind_expectation]
  have hinner : ∀ r : ZMod 2,
      ∑' L : List (ZMod 2), ((idealFreshRecords 1 i).map fun L => r :: L) L * missWeight h L =
        ∑' L : List (ZMod 2), (idealFreshRecords 1 i) L * missWeight h (r :: L) := by
    intro r
    exact pmf_map_expectation _ _ _
  simp only [hinner, missWeight_cons]
  have hite : ∀ r : ZMod 2,
      ∑' L : List (ZMod 2), (idealFreshRecords 1 i) L * (if r = h then 0 else missWeight h L) =
        if r = h then 0
        else ∑' L : List (ZMod 2), (idealFreshRecords 1 i) L * missWeight h L := by
    intro r
    by_cases hr : r = h <;> simp [hr]
  simp only [hite]
  have hconst : ∀ r : ZMod 2, (PMF.uniformOfFintype' (ZMod 2)) r
      = (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ := fun r => PMF.uniformOfFintype'_apply r
  simp only [hconst]
  rw [ENNReal.tsum_mul_left, zmod_two_tsum_ite]

/-- The probability that `i` independent uniform records modulo two miss a fixed target is `(1 /
2) ^ i`. -/
theorem freshMiss_eq (h : ZMod 2) (i : ℕ) :
    ∑' L : List (ZMod 2), (idealFreshRecords 1 i) L * missWeight h L
      = ((2 : ℝ≥0∞)⁻¹) ^ i := by
  induction i with
  | zero =>
    rw [freshMiss_zero, pow_zero]
  | succ i ih =>
    rw [freshMiss_succ, ih,
      show (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ by rw [ZMod.card]; norm_num,
      pow_succ, mul_comm]

/-- The base sieve run at modulus two and depth zero has failure mass `2 ^ (-24)`. -/
theorem sieveRun_one_none (s : ZMod 2) :
    (dihedralSieveRun 1 0 s).1 none = ENNReal.ofReal ((2:ℝ) ^ (-24 : ℝ)) := by
  have hrun : (dihedralSieveRun 1 0 s).1 =
      ((idealFreshRecords 1 (24 * 2 ^ (3 * 0))).bind (idealSieveRec 1 0 0)).bind
        (idealReadout 1 s) := rfl
  rw [hrun]
  have hP : (idealFreshRecords 1 (24 * 2 ^ (3 * 0))).bind (idealSieveRec 1 0 0)
      = (idealFreshRecords 1 24 : PMF (List (ZMod 2))) := by
    have h24 : 24 * 2 ^ (3 * 0) = 24 := rfl
    rw [h24]
    have hj : idealSieveRec 1 0 0 = (pure : List (ZMod 2) → PMF (List (ZMod 2))) := rfl
    rw [hj]
    exact PMF.bind_pure _
  rw [hP, PMF.bind_apply]
  have hpt : ∀ L : List (ZMod 2),
      (idealFreshRecords 1 24) L * (idealReadout 1 s L) none =
        (idealFreshRecords 1 24) L * missWeight ((2 ^ (1 - 1) : ℕ) : ZMod 2) L := by
    intro L
    rw [idealReadout_none]
    rfl
  simp only [hpt]
  show ∑' L : List (ZMod 2),
      (idealFreshRecords 1 24) L * missWeight ((2 ^ (1 - 1) : ℕ) : ZMod 2) L =
    ENNReal.ofReal ((2:ℝ) ^ (-24 : ℝ))
  rw [freshMiss_eq]
  have heq : ((2 : ℝ≥0∞)⁻¹) ^ 24 = ENNReal.ofReal ((2:ℝ) ^ (-24 : ℝ)) := by
    have hpow : (2:ℝ) ^ (-24 : ℝ) = ((2:ℝ) ^ 24)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
      congr 1
      exact Real.rpow_natCast 2 24
    rw [hpow, ENNReal.ofReal_inv_of_pos (by positivity)]
    have h2 : ENNReal.ofReal ((2:ℝ) ^ 24) = (2 : ℝ≥0∞) ^ 24 := by
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2:ℝ))]
      norm_num
    rw [h2, ENNReal.inv_pow]
  rw [heq]

/-- The sieve failure mass equals one minus the mass of final lists containing the target label. -/
theorem sieveRun_none (n m : ℕ) (s : ZMod (2 ^ n)) :
    (dihedralSieveRun n m s).1 none =
      1 - ∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then
          ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L else 0 := by
  have hbind : (dihedralSieveRun n m s).1 =
      ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)).bind
        (idealReadout n s) := rfl
  rw [hbind, PMF.bind_apply]
  have hpt : ∀ L : List (ZMod (2 ^ n)),
      ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L *
          (idealReadout n s L) none =
        ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L *
          (if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 0 else 1) := by
    intro L
    rw [idealReadout_none]
  simp only [hpt]
  set P := (idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)
  set h := ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))
  have hsplit : ∀ L : List (ZMod (2 ^ n)),
      P L * (if h ∈ L then 0 else 1) = if h ∈ L then 0 else P L := by
    intro L
    by_cases hh : h ∈ L <;> simp [hh]
  simp only [hsplit]
  have hsum : ∑' L : List (ZMod (2 ^ n)), P L = 1 := PMF.tsum_coe P
  have hdecomp : ∀ L : List (ZMod (2 ^ n)),
      P L = (if h ∈ L then P L else 0) + (if h ∈ L then 0 else P L) := by
    intro L
    by_cases hh : h ∈ L <;> simp [hh]
  have h1 : (∑' L : List (ZMod (2 ^ n)), (if h ∈ L then P L else 0)) +
      (∑' L : List (ZMod (2 ^ n)), (if h ∈ L then 0 else P L)) = 1 := by
    rw [← ENNReal.tsum_add]
    have hfe : (fun L : List (ZMod (2 ^ n)) =>
        (if h ∈ L then P L else 0) + (if h ∈ L then 0 else P L)) = P :=
      funext fun L => (hdecomp L).symm
    rw [hfe]
    exact hsum
  have h2 : (∑' L : List (ZMod (2 ^ n)), (if h ∈ L then 0 else P L)) +
      (∑' L : List (ZMod (2 ^ n)), (if h ∈ L then P L else 0)) = 1 := by
    rw [add_comm]
    exact h1
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top h2

/-- For positive `u`, `exp (-u)` is at most one. -/
theorem exp_bound (u : ℝ) (hu : 0 < u) : Real.exp (-u) ≤ 1 := by
  have he : Real.exp (-u) ≤ Real.exp 0 :=
    Real.exp_le_exp.mpr (neg_nonpos.mpr (le_of_lt hu))
  rw [Real.exp_zero] at he
  exact he

/-- At the prescribed square-root depth and exponent at least two, the sieve failure mass is
bounded by the complement of the stated exponential expression. -/
theorem sieveRun_none_le (n m : ℕ) (s : ZMod (2 ^ n)) (hn : 2 ≤ n)
    (hm : m = Nat.ceil (Real.sqrt ((n : ℝ) - 1))) :
    (dihedralSieveRun n m s).1 none ≤
      ENNReal.ofReal (1 - (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) := by
  have hu : (0:ℝ) < (2:ℝ)^((m:ℝ)/3 - 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase : (0:ℝ) ≤ 1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2)) :=
    sub_nonneg.2 (exp_bound _ hu)
  have hx : 0 ≤ (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m := pow_nonneg hbase m
  have hhit : ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) ≤
      ∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then
          ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L else 0 :=
    dihedralSieveIdealHit n m hn hm
  rw [sieveRun_none]
  have hsub : (1 : ℝ≥0∞) -
      (∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then
          ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L else 0) ≤
      1 - ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) :=
    tsub_le_tsub_left hhit 1
  have hof : (1 : ℝ≥0∞) - ENNReal.ofReal ((1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m)
      = ENNReal.ofReal (1 - (1 - Real.exp (-(2:ℝ)^((m:ℝ)/3 - 2))) ^ m) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hx]
  exact hsub.trans (le_of_eq hof)

/-- The nonnegative part of `levelSuccessBound` is bounded by the uncorrected exponential sieve
expression. -/
theorem levelSuccessBound_le (k : ℕ) :
    max 0 (levelSuccessBound k) ≤
      (1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k := by
  unfold levelSuccessBound
  have hx : (0:ℝ) ≤ (2:ℝ) ^ (-((2 ^ levelWidth k : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsub : (1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k -
      (2:ℝ) ^ (-((2 ^ levelWidth k : ℕ) : ℝ)) ≤
      (1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k :=
    sub_le_self _ hx
  have hu : (0:ℝ) < (2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnn : (0:ℝ) ≤ (1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k :=
    pow_nonneg (sub_nonneg.2 (exp_bound _ hu)) _
  exact max_le hnn hsub

/-- The uncorrected exponential sieve expression is at most one. -/
theorem levelSuccessBound_le_one (k : ℕ) :
    (1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2))) ^ levelWidth k ≤ 1 := by
  have hu : (0:ℝ) < (2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (0:ℝ) ≤ 1 - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2)) :=
    sub_nonneg.2 (exp_bound _ hu)
  have h2 : (1:ℝ) - Real.exp (-(2:ℝ) ^ ((levelWidth k : ℝ) / 3 - 2)) ≤ 1 :=
    sub_le_self _ (le_of_lt (Real.exp_pos _))
  exact pow_le_one₀ h1 h2

/-- Every repeated-level term in the descent failure estimate is nonnegative. -/
theorem dfb_term_nonneg (k : ℕ) :
    0 ≤ (1 - max 0 (levelSuccessBound k)) ^ levelTrials k := by
  apply pow_nonneg
  have h := levelSuccessBound_le k
  have h1 := levelSuccessBound_le_one k
  linarith

/-- The descent failure bound is nonnegative. -/
theorem dfb_nonneg (n : ℕ) : 0 ≤ descentFailureBound n := by
  unfold descentFailureBound
  apply add_nonneg
  · exact Real.rpow_nonneg (by norm_num) _
  · exact Finset.sum_nonneg fun k _ => dfb_term_nonneg k

/-- The level width at one is zero. -/
theorem levelWidth_one : levelWidth 1 = 0 := by
  unfold levelWidth
  push_cast
  rw [sub_self, Real.sqrt_zero, Nat.ceil_zero]

/-- At exponent one, the descent failure bound is `2 ^ (-(24 * levelTrials 1))`. -/
theorem dfb_one : descentFailureBound 1 = (2:ℝ) ^ (-(24 * levelTrials 1 : ℝ)) := by
  unfold descentFailureBound
  rw [show (Finset.Icc 2 1 : Finset ℕ) = ∅ by simp, Finset.sum_empty, add_zero]

/-- For positive `n`, the next descent failure bound adds the repeated failure term for level `n
+ 1`. -/
theorem dfb_succ (n : ℕ) (hn : 1 ≤ n) :
    descentFailureBound (n + 1) =
      descentFailureBound n +
        (1 - max 0 (levelSuccessBound (n + 1))) ^ levelTrials (n + 1) := by
  unfold descentFailureBound
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
  ring

/-- Recursive descent failure splits into failure at the current level and weighted failures of
the two restricted descents. -/
theorem slopeDescent_none_succ_succ {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (k : ℕ) (f : DihedralReg (2 ^ (k + 2)) → S) :
    slopeDescent (k + 2) S f none =
      (levelRunTrials (k + 2) f) none +
        ∑ b : Bool, (levelRunTrials (k + 2) f) (some b) *
          slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b) none := by
  rw [slopeDescent_ss k f, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  show (levelRunTrials (k + 2) f) none * (PMF.pure (none : Option (ZMod (2 ^ (k + 2))))) none +
    (∑ b : Bool, (levelRunTrials (k + 2) f) (some b) *
      ((slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b)).map
        fun o => o.map fun t => parityLift (k + 1) b t) none) =
      (levelRunTrials (k + 2) f) none +
        ∑ b : Bool, (levelRunTrials (k + 2) f) (some b) *
          slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b) none
  have h1 : (PMF.pure (none : Option (ZMod (2 ^ (k + 2))))) none = 1 :=
    PMF.pure_apply_self none
  have h2 : ∀ b : Bool,
      ((slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b)).map
        fun o => o.map fun t => parityLift (k + 1) b t) none =
      slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b) none :=
    fun b => optionMap_none _ _
  rw [h1, mul_one]
  simp only [h2]

/-- For a reflection-hiding oracle, the failure mass of slope descent is at most `ENNReal.ofReal
(descentFailureBound n)`. -/
theorem descent_fail_bound :
    ∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
    DihedralReflectionHides (2 ^ n) f s →
    slopeDescent n S f none ≤ ENNReal.ofReal (descentFailureBound n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro S _ _ _ f s hf
    cases n with
    | zero =>
      rw [slopeDescent_zero]
      show (PMF.pure (some 0) : PMF (Option (ZMod (2 ^ 0)))) none ≤ _
      rw [PMF.pure_apply_of_ne _ _
        (show (none : Option (ZMod (2 ^ 0))) ≠ some 0 by simp)]
      exact bot_le
    | succ n1 =>
      cases n1 with
      | zero =>
        erw [slopeDescent_one, optionMap_none]
        have htr : (levelRunTrials 1 f) none = (levelRun 1 f none) ^ levelTrials 1 :=
          firstAnswer_none _ _
        have hrun : levelRun 1 f = (dihedralSieveRun 1 0 s).1 := by
          unfold levelRun
          rw [levelWidth_one]
          exact dihedralSieveBridge 1 0 S f s hf
        rw [htr, hrun, sieveRun_one_none s, dfb_one]
        have hpow24 : ((2:ℝ) ^ (-24 : ℝ)) ^ levelTrials 1
            = (2:ℝ) ^ (-(24 * levelTrials 1 : ℝ)) := by
          rw [← Real.rpow_natCast _ (levelTrials 1),
            ← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ))]
          congr 1
          push_cast
          ring
        rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) (-24 : ℝ))]
        exact ENNReal.ofReal_le_ofReal (le_of_eq hpow24)
      | succ k =>
        have hdef : slopeDescent (Nat.succ (Nat.succ k)) S f
            = slopeDescent (k + 2) S f := rfl
        rw [hdef, slopeDescent_none_succ_succ k f]
        have hsum : ∑ b : Bool, (levelRunTrials (k + 2) f) (some b) *
            slopeDescent (k + 1) S (parityRestrictedOracle (k + 1) f b) none =
            (levelRunTrials (k + 2) f) (some (decide (s.val % 2 = 1))) *
              slopeDescent (k + 1) S
                (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) none := by
          refine Finset.sum_eq_single_of_mem (decide (s.val % 2 = 1)) (Finset.mem_univ _) ?_
          intro b _ hbb
          rw [levelRun_wrong_zero f s hf b hbb, zero_mul]
        rw [hsum]
        have huniq := parityLift_unique (k + 1) s
        obtain ⟨tstar, hlift, hunique⟩ := huniq
        have hres : DihedralReflectionHides (2 ^ (k + 1))
            (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) tstar := by
          apply parityRestriction_hides (k + 1) f (decide (s.val % 2 = 1)) tstar
          rw [hlift]
          exact hf
        have ih' : slopeDescent (k + 1) S
            (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) none ≤
            ENNReal.ofReal (descentFailureBound (k + 1)) :=
          ih (k + 1) (by omega) S
            (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) tstar hres
        have hp_le1 : (levelRunTrials (k + 2) f) (some (decide (s.val % 2 = 1))) ≤ 1 :=
          PMF.coe_le_one _ _
        have hprod : (levelRunTrials (k + 2) f) (some (decide (s.val % 2 = 1))) *
            slopeDescent (k + 1) S
              (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) none ≤
            ENNReal.ofReal (descentFailureBound (k + 1)) :=
          le_trans (mul_le_mul hp_le1 ih' bot_le bot_le)
            (le_of_eq (one_mul (ENNReal.ofReal (descentFailureBound (k + 1)))))
        have htr : (levelRunTrials (k + 2) f) none
            = (levelRun (k + 2) f none) ^ levelTrials (k + 2) :=
          firstAnswer_none _ _
        have hrun : levelRun (k + 2) f
            = (dihedralSieveRun (k + 2) (levelWidth (k + 2)) s).1 :=
          dihedralSieveBridge (k + 2) (levelWidth (k + 2)) S f s hf
        have hbase : (dihedralSieveRun (k + 2) (levelWidth (k + 2)) s).1 none ≤
            ENNReal.ofReal (1 -
              (1 - Real.exp (-(2:ℝ)^(((levelWidth (k + 2) : ℝ)/3 - 2)))) ^ levelWidth (k + 2)) :=
          sieveRun_none_le (k + 2) (levelWidth (k + 2)) s (by omega) rfl
        have hle : (1:ℝ) -
            (1 - Real.exp (-(2:ℝ)^(((levelWidth (k + 2) : ℝ)/3 - 2)))) ^ levelWidth (k + 2) ≤
            1 - max 0 (levelSuccessBound (k + 2)) :=
          sub_le_sub_left (levelSuccessBound_le (k + 2)) 1
        have hbase' : (dihedralSieveRun (k + 2) (levelWidth (k + 2)) s).1 none ≤
            ENNReal.ofReal (1 - max 0 (levelSuccessBound (k + 2))) :=
          hbase.trans (ENNReal.ofReal_le_ofReal hle)
        have hpow1 : (levelRunTrials (k + 2) f) none ≤
            ENNReal.ofReal ((1 - max 0 (levelSuccessBound (k + 2))) ^ levelTrials (k + 2)) := by
          rw [htr, hrun]
          have hpp := pow_le_pow_left' hbase' (levelTrials (k + 2))
          have hz : 0 ≤ (1:ℝ) - max 0 (levelSuccessBound (k + 2)) := by
            have := levelSuccessBound_le (k + 2)
            have := levelSuccessBound_le_one (k + 2)
            linarith
          rw [ENNReal.ofReal_pow hz]
          exact hpp
        have hdfb : descentFailureBound (k + 2) =
            descentFailureBound (k + 1) +
              (1 - max 0 (levelSuccessBound (k + 2))) ^ levelTrials (k + 2) :=
          dfb_succ (k + 1) (by omega)
        have hof : ENNReal.ofReal (descentFailureBound (k + 2)) =
            ENNReal.ofReal ((1 - max 0 (levelSuccessBound (k + 2))) ^ levelTrials (k + 2)) +
              ENNReal.ofReal (descentFailureBound (k + 1)) := by
          rw [hdfb, ENNReal.ofReal_add (dfb_nonneg _) (dfb_term_nonneg _)]
          rw [add_comm]
        have hcomp : (levelRunTrials (k + 2) f) none +
            (levelRunTrials (k + 2) f) (some (decide (s.val % 2 = 1))) *
              slopeDescent (k + 1) S
                (parityRestrictedOracle (k + 1) f (decide (s.val % 2 = 1))) none ≤
            ENNReal.ofReal ((1 - max 0 (levelSuccessBound (k + 2))) ^ levelTrials (k + 2)) +
              ENNReal.ofReal (descentFailureBound (k + 1)) :=
          add_le_add hpow1 hprod
        have hbridge : ENNReal.ofReal (descentFailureBound (k + 1 + 1))
            = ENNReal.ofReal (descentFailureBound (k + 2)) := rfl
        rw [hbridge, hof]
        exact hcomp

/-- Collect binary reconstruction, error-free slope outputs, the descent failure estimate,
record counts, and sorting time and space bounds for the dihedral descent construction
[Kuperberg2005]. -/
theorem clause16 :

  ((∀ (n : ℕ) (s : ZMod (2 ^ n)), slopeOfBits n (slopeBit n s) = s) ∧
    (∀ (n : ℕ) (b : ℕ → Bool) (i : ℕ), i < n →
      slopeBit n (slopeOfBits n b) i = b i)) ∧

  ((∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
    DihedralReflectionHides (2 ^ n) f s →
      (∀ s' : ZMod (2 ^ n), s' ≠ s → slopeDescent n S f (some s') = 0) ∧
      slopeDescent n S f (some s) = 1 - slopeDescent n S f none) ∧
    (∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
    DihedralReflectionHides (2 ^ n) f s →
      slopeDescent n S f none ≤ ENNReal.ofReal (descentFailureBound n))) ∧

  ((∀ n : ℕ, descentRecords n = sourcePowerTwoQueryBudget n)) ∧

  ((∀ (α : Type) (key : α → ℕ) (L : List α),
      List.Perm (sortRecords key L) L ∧ (sortRecords key L).length = L.length) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α), sortedByKey key (sortRecords key L)) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      sortCompareCount key L ≤ L.length * L.length) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α)
      (p : α × α), p ∈ sortedPairs key (sortRecords key L) → key p.1 = key p.2) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      2 * (sortedPairs key (sortRecords key L)).length ≤ L.length) ∧
    (∀ (n w t : ℕ) (α : Type) [DecidableEq α] (label : α → ZMod (2 ^ n))
      (L : List α),
      (sievePairWith n label w t L).length =
        (sortedPairs (fun r => windowKey n w t (label r))
          (sortRecords (fun r => windowKey n w t (label r)) L)).length)) ∧

  ((∀ (α : Type) (key : α → ℕ) (L : List α) (k : ℕ),
      sortCompareCount key L * (k + 1) ≤ sortBitTime k L.length) ∧
    (∀ (n : ℕ),
      descentBitTime n ≤
        ∑ k ∈ Finset.Icc 1 n, 2 * (levelTrials k * levelRecords k) ^ 2 * (k + 1)) ∧
    (∀ (n k : ℕ), k ∈ Finset.Icc 1 n →
      sortSpace k (levelTrials k * levelRecords k) ≤ descentSpace n) ∧
    (∀ (n : ℕ),
      descentSpace n ≤ ∑ k ∈ Finset.Icc 1 n, levelTrials k * levelRecords k * k))
:= by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro n s
    exact slopeOfBits_slopeBit n s
  · intro n b i hi
    exact slopeBit_slopeOfBits n b i hi
  · intro n S _ _ _ f s hf
    exact ⟨descent_wrong_zero n S f s hf, descent_mass n f s hf⟩
  · intro n S _ _ _ f s hf
    exact descent_fail_bound n S f s hf
  · intro n
    exact descentRecords_eq n
  · intro α key L
    exact sortRecords_perm key L
  · intro α key L
    exact sortRecords_sorted key L
  · intro α key L
    exact sortCompareCount_le key L
  · intro α key L p hp
    exact sortedPairs_keys key (sortRecords key L) p hp
  · intro α key L
    exact (sortedPairs_len_le key (sortRecords key L)).trans
      (le_of_eq (sortRecords_perm key L).2)
  · intro n w t α _ label L
    exact sievePairWith_sorted_count n w t α label L
  · intro α key L k
    exact sortBitTime_bound key L k
  · intro n
    exact descentBitTime_bound n
  · intro n k hk
    exact descentSpace_ge n k hk
  · intro n
    exact descentSpace_le n

end Qatlib.Concepts.HspRecovery.RecordExtract
