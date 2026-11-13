/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshFallback.BitScanLedger.CountedFreshFallbackDefs

/-!
# Counted fresh-string fallback

This module proves correctness and bit-read bounds for the explicit comparisons and history
scans used by `runFallback`. The implementation returns the same fresh string as
`samplerFallback` and records both bit reads and binary-prefix generator visits.

The finite classical searches support oracle-circuit resource analysis in the computational
setting of [KitaevShenVyalyi2002]. A history shorter than the binary alphabet guarantees that
fallback returns an unused string.

## Main statements

* `compare_and_membership_correct`: proves word equality and membership tests with their read
  bounds.
* `firstFreshScan_correct_and_reads`: identifies the first fresh candidate and bounds its scan
  cost.
* `runFallback_correct_and_budget`: combines semantic correctness, both ledgers, and existence
  of a fresh result.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.FreshFallback.BitScanLedger

open Qatlib.Concepts.FreshFallback.BitScanLedger

/-- The bit comparator returns true exactly when the two words agree at every listed address,
and records exactly twice the address-list length in reads. -/
theorem compareBits_correct {n : ℕ} (x y : Reg n) (addresses : List (Fin n)) :
    ((compareBits x y addresses).1 = true ↔ ∀ i ∈ addresses, x i = y i) ∧
      (compareBits x y addresses).2 = 2 * addresses.length := by
  induction addresses with
  | nil => simp [compareBits]
  | cons i addresses ih =>
    constructor
    · simp [compareBits, Bool.and_eq_true, ih.1]
    · simp [compareBits, ih.2, Nat.mul_add, Nat.add_comm]

/-- The full-word comparator returns true exactly when its two words are equal and records
exactly `2 * n` bit reads. -/
theorem compareWord_correct {n : ℕ} (x y : Reg n) :
    ((compareWord x y).1 = true ↔ x = y) ∧ (compareWord x y).2 = 2 * n := by
  have h := compareBits_correct x y (List.finRange n)
  constructor
  · simpa [compareWord, funext_iff] using h.1
  · simpa [compareWord] using h.2

/-- The history membership scan returns true exactly on members and uses at most `2 * n *
hist.length` bit reads. -/
theorem memberScan_correct {n : ℕ} (x : Reg n) (hist : List (Reg n)) :
    ((memberScan x hist).1 = true ↔ x ∈ hist) ∧
      (memberScan x hist).2 ≤ 2 * n * hist.length := by
  induction hist with
  | nil => simp [memberScan]
  | cons y hist ih =>
    have hc := compareWord_correct x y
    by_cases hxy : x = y
    · have hb := hc.1.mpr hxy
      constructor
      · simp only [memberScan, hb, ↓reduceIte]
        simp [hxy]
      · simp only [memberScan, hb, ↓reduceIte, hc.2,
          List.length_cons]
        nlinarith
    · have hb : (compareWord x y).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hxy (hc.1.mp h))
      constructor
      · simp [memberScan, hb, ih.1, hxy]
      · simp only [memberScan, hb, Bool.false_eq_true, ↓reduceIte, hc.2,
          List.length_cons]
        nlinarith [ih.2]

/-- Packages correctness and read counts for full-word comparison and history membership
scanning. -/
theorem compare_and_membership_correct :
    ∀ (n : ℕ) (x y : Reg n),
      ((compareWord x y).1 = true ↔ x = y) ∧ (compareWord x y).2 = 2 * n ∧
        ∀ hist : List (Reg n),
          ((memberScan x hist).1 = true ↔ x ∈ hist) ∧
            (memberScan x hist).2 ≤ 2 * n * hist.length := by
  intro n x y
  exact ⟨(compareWord_correct x y).1, (compareWord_correct x y).2,
    memberScan_correct x⟩

/-- The fresh-candidate scan returns the first candidate absent from the history and uses at
most `2 * n * hist.length * candidates.length` bit reads. -/
theorem firstFreshScan_correct_and_reads :
    ∀ (n : ℕ) (hist candidates : List (Reg n)),
      (firstFreshScan hist candidates).1 = candidates.find? (fun x => decide (x ∉ hist)) ∧
        (firstFreshScan hist candidates).2 ≤ 2 * n * hist.length * candidates.length := by
  intro n hist candidates
  induction candidates with
  | nil => simp [firstFreshScan]
  | cons x candidates ih =>
    have hm := memberScan_correct x hist
    by_cases hx : x ∈ hist
    · have hb := hm.1.mpr hx
      constructor
      · simp [firstFreshScan, hb, hx, ih.1]
      · simp only [firstFreshScan, hb, ↓reduceIte,
          List.length_cons]
        nlinarith [hm.2, ih.2]
    · have hb : (memberScan x hist).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hx (hm.1.mp h))
      constructor
      · simp [firstFreshScan, hb, hx]
      · simp only [firstFreshScan, hb, Bool.false_eq_true, ↓reduceIte,
          List.length_cons]
        nlinarith [hm.2]

/-- If the history has length less than `2^n`, the binary-alphabet fresh-string search cannot
return `none`. -/
theorem firstFresh_ne_none_of_length_lt (n : ℕ) (hist : List (Reg n))
    (hlen : hist.length < 2 ^ n) : firstFresh n hist ≠ none := by
  intro hnone
  have hsub : binaryAlphabet n ⊆ hist :=
    fun x _ => (firstFresh_eq_none_iff n hist).mp hnone x
  have hcard := ((binaryAlphabet_nodup n).subperm hsub).length_le
  rw [binaryAlphabet_length] at hcard
  omega

/-- The counted fallback agrees with `samplerFallback`, uses at most `2 * n * L * (L + 2)` bit
reads and `(2 * n + 1) * (L + 1) + 1` generator visits, where `L = hist.length`. If `L <
2^n`, it returns a string absent from the history. -/
theorem runFallback_correct_and_budget :
    ∀ (n : ℕ) (hist : List (Reg n)) (x : Reg n),
      (runFallback n hist x).1.1 = samplerFallback n hist x ∧
        (runFallback n hist x).1.2 ≤ 2 * n * hist.length * (hist.length + 2) ∧
        (runFallback n hist x).2 ≤ (2 * n + 1) * (hist.length + 1) + 1 ∧
        (hist.length < 2 ^ n →
          ∃ y, (runFallback n hist x).1.1 = some y ∧ y ∉ hist) := by
  intro n hist x
  have hm := memberScan_correct x hist
  have hmain : (runFallback n hist x).1.1 = samplerFallback n hist x ∧
      (runFallback n hist x).1.2 ≤ 2 * n * hist.length * (hist.length + 2) ∧
      (runFallback n hist x).2 ≤ (2 * n + 1) * (hist.length + 1) + 1 := by
    by_cases hx : x ∈ hist
    · have hb := hm.1.mpr hx
      have hs := firstFreshScan_correct_and_reads n hist
        (binaryPrefixCounted n (hist.length + 1)).1
      have hlength : (binaryPrefixCounted n (hist.length + 1)).1.length ≤
          hist.length + 1 := by
        rw [binaryPrefixCounted_value, List.length_take]
        exact Nat.min_le_left _ _
      simp only [runFallback, hb, ↓reduceIte]
      refine ⟨?_, ?_, binaryPrefixCounted_visits n (hist.length + 1)⟩
      · rw [hs.1]
        simpa only [samplerFallback, if_pos hx, firstFreshBounded] using
          firstFreshBounded_eq_firstFresh n hist
      · calc
          _ ≤ 2 * n * hist.length +
              2 * n * hist.length * (binaryPrefixCounted n (hist.length + 1)).1.length :=
            Nat.add_le_add hm.2 hs.2
          _ ≤ 2 * n * hist.length + 2 * n * hist.length * (hist.length + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hlength) _
          _ = 2 * n * hist.length * (hist.length + 2) := by ring
    · have hb : (memberScan x hist).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hx (hm.1.mp h))
      simp only [runFallback, hb, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [samplerFallback, hx], ?_, Nat.zero_le _⟩
      calc
        _ ≤ 2 * n * hist.length := hm.2
        _ ≤ 2 * n * hist.length * (hist.length + 2) :=
          Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨hmain.1, hmain.2.1, hmain.2.2, ?_⟩
  intro hlen
  have hnon : samplerFallback n hist x ≠ none := by
    by_cases hx : x ∈ hist
    · simpa only [samplerFallback, if_pos hx] using
        firstFresh_ne_none_of_length_lt n hist hlen
    · simp [samplerFallback, hx]
  cases hout : samplerFallback n hist x with
  | none => exact False.elim (hnon hout)
  | some y =>
    exact ⟨y, hmain.1.trans hout, samplerFallback_fresh n hist x y hout⟩

end Qatlib.Concepts.FreshFallback.BitScanLedger
