/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchInstance

/-!
# Translation symmetry of ordered-search oracles

Defines the integer comparison oracle `paperF` and its periodic doubled-space form `paperG` from
[ChildsLandahlParrilo2007]. The identities describe translation covariance, period `2 * N`, and
sign reversal under a half-period shift.

`paperG_eq_ospBit` identifies this sign convention with the Boolean oracle used by the
translation-invariant semidefinite bridge.

## Main statements

* `paperG_piecewise`: recovers the comparison oracle on each half of the doubled domain.
* `paperG_shift`: expresses translation covariance.

## References

* [Childs et al., 2007][ChildsLandahlParrilo2007]
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.OrderedSearch06.OracleSymmetry

/-- The integer comparison sign, equal to −1 when `x < j` and 1 otherwise. -/
def paperF (j x : ℤ) : ℤ := if x < j then -1 else 1

/-- For `x ≥ 1`, increasing the comparison threshold by one is equivalent to decreasing the
query position by one [ChildsLandahlParrilo2007]. -/
theorem paperF_succ_eq (j x : ℤ) (hx : 1 ≤ x) :
    paperF (j + 1) x = paperF j (x - 1) := by
  unfold paperF
  by_cases h : x < j + 1
  · have h' : x - 1 < j := by omega
    rw [if_pos h, if_pos h']
  · have h' : ¬ (x - 1 < j) := by omega
    rw [if_neg h, if_neg h']

/-- For `j ≥ 0`, the comparison sign at position zero and threshold `j + 1` is −1. -/
theorem paperF_zero (j : ℤ) (hj : 0 ≤ j) : paperF (j + 1) 0 = -1 := by
  unfold paperF
  rw [if_pos (by omega)]

/-- The periodic ordered-search sign determined by whether `(x − j) mod (2 * N)` lies in the
first half. -/
def paperG (N : ℕ) (j x : ℤ) : ℤ :=
  if (x - j) % ((2 * N : ℕ) : ℤ) < (N : ℤ) then 1 else -1

/-- For a representative in `[0, 2 * N)`, shifting by `N` exchanges the first-half and
second-half tests. -/
theorem paperG_half_test (N : ℕ) (hN : 0 < N) {a : ℤ} (ha0 : 0 ≤ a)
    (ham : a < 2 * (N : ℤ)) :
    ((a + (N : ℤ)) % (2 * (N : ℤ)) < (N : ℤ)) ↔ ¬ (a < (N : ℤ)) := by
  by_cases h : a < (N : ℤ)
  · have h1 : 0 ≤ a + (N : ℤ) := by omega
    have h2 : a + (N : ℤ) < 2 * (N : ℤ) := by omega
    rw [Int.emod_eq_of_lt h1 h2]
    omega
  · have hge : (N : ℤ) ≤ a := by omega
    have he : a + (N : ℤ) = (a - (N : ℤ)) + (2 * (N : ℤ)) * 1 := by ring
    rw [he, Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- For positive `N`, the remainder of `−N` modulo `2 * N` is `N`. -/
theorem paperG_neg_half (N : ℕ) (hN : 0 < N) :
    (-(N : ℤ)) % (2 * (N : ℤ)) = (N : ℤ) := by
  have hn0 : 0 ≤ (N : ℤ) := by positivity
  have hn2 : (N : ℤ) < 2 * (N : ℤ) := by omega
  rw [show (-(N : ℤ)) = (N : ℤ) + (2 * (N : ℤ)) * (-1) by ring,
    Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt hn0 hn2

/-- Adding `−N` or `N` gives the same remainder modulo `2 * N`. -/
theorem paperG_add_neg_half (N : ℕ) (hN : 0 < N) (b : ℤ) :
    (b + (-(N : ℤ))) % (2 * (N : ℤ)) = (b + (N : ℤ)) % (2 * (N : ℤ)) := by
  refine (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr ?_
  rw [show (b + (-(N : ℤ))) - (b + (N : ℤ)) = -(2 * (N : ℤ)) by ring]
  exact Int.emod_eq_zero_of_dvd (dvd_neg.mpr dvd_rfl)

/-- On the doubled domain with threshold in the first half, `paperG` equals `paperF` on the
first half and its negated translated value on the second half [ChildsLandahlParrilo2007]. -/
theorem paperG_piecewise (N : ℕ) (hN : 0 < N) (j x : ℤ) (hj0 : 0 ≤ j)
    (hjN : j < (N : ℤ)) (hx0 : 0 ≤ x) (hx : x < 2 * (N : ℤ)) :
    paperG N j x = if x < (N : ℤ) then paperF j x else -paperF j (x - (N : ℤ)) := by
  unfold paperG paperF
  push_cast
  have hm : (0 : ℤ) < 2 * (N : ℤ) := by positivity
  by_cases hxN : x < (N : ℤ)
  · rw [if_pos hxN]
    by_cases hxj : x < j
    · have hlo : -(2 * (N : ℤ)) < x - j := by omega
      have hlt0 : x - j < 0 := by omega
      have hmid : 0 ≤ x - j + 2 * (N : ℤ) := by omega
      have hmid2 : x - j + 2 * (N : ℤ) < 2 * (N : ℤ) := by omega
      have he : x - j = (x - j + 2 * (N : ℤ)) + (2 * (N : ℤ)) * (-1) := by ring
      have : (x - j) % (2 * (N : ℤ)) = x - j + 2 * (N : ℤ) := by
        conv_lhs => rw [he]
        rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hmid hmid2]
      rw [this, if_pos hxj, if_neg (by omega : ¬ (x - j + 2 * (N : ℤ) < (N : ℤ)))]
    · have hge : j ≤ x := by omega
      have hmid : 0 ≤ x - j := by omega
      have hmid2 : x - j < 2 * (N : ℤ) := by omega
      have : (x - j) % (2 * (N : ℤ)) = x - j := Int.emod_eq_of_lt hmid hmid2
      rw [this, if_neg hxj, if_pos (by omega : x - j < (N : ℤ))]
  · rw [if_neg hxN]
    by_cases hxj : x - (N : ℤ) < j
    · have hmid : 0 ≤ x - j := by omega
      have hmid2 : x - j < 2 * (N : ℤ) := by omega
      have hlt : x - j < (N : ℤ) := by omega
      have : (x - j) % (2 * (N : ℤ)) = x - j := Int.emod_eq_of_lt hmid hmid2
      rw [this, if_pos hlt, if_pos (by omega : x - (N : ℤ) < j)]
      norm_num
    · have hmid : (N : ℤ) ≤ x - j := by omega
      have hmid2 : x - j < 2 * (N : ℤ) := by omega
      have : (x - j) % (2 * (N : ℤ)) = x - j := Int.emod_eq_of_lt (by omega) hmid2
      rw [this, if_neg (by omega : ¬ (x - j < (N : ℤ))), if_neg (by omega : ¬ (x - (N : ℤ) < j))]

/-- Shifting the threshold by `N` negates `paperG` for positive `N` [ChildsLandahlParrilo2007]. -/
theorem paperG_add_half (N : ℕ) (hN : 0 < N) (j x : ℤ) :
    paperG N (j + (N : ℤ)) x = -paperG N j x := by
  unfold paperG
  push_cast
  have hm : (0 : ℤ) < 2 * (N : ℤ) := by positivity
  have hkey : (x - (j + (N : ℤ))) % (2 * (N : ℤ)) =
      ((x - j) % (2 * (N : ℤ)) + (N : ℤ)) % (2 * (N : ℤ)) := by
    rw [show x - (j + (N : ℤ)) = (x - j) + (-(N : ℤ)) by ring, Int.add_emod,
      paperG_neg_half N hN]
  rw [hkey]
  set a : ℤ := (x - j) % (2 * (N : ℤ)) with ha
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by omega)
  have ham : a < 2 * (N : ℤ) := Int.emod_lt_of_pos _ hm
  rw [if_congr (paperG_half_test N hN ha0 ham) rfl rfl]
  by_cases h : a < (N : ℤ) <;> simp [h]

/-- Shifting the query position by `N` negates `paperG` for positive `N`
[ChildsLandahlParrilo2007]. -/
theorem paperG_query_half (N : ℕ) (hN : 0 < N) (j x : ℤ) :
    paperG N j (x + (N : ℤ)) = -paperG N j x := by
  unfold paperG
  push_cast
  have hm : (0 : ℤ) < 2 * (N : ℤ) := by positivity
  have hNm : (N : ℤ) % (2 * (N : ℤ)) = (N : ℤ) :=
    Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le N) (by omega)
  have hkey : (x + (N : ℤ) - j) % (2 * (N : ℤ)) =
      ((x - j) % (2 * (N : ℤ)) + (N : ℤ)) % (2 * (N : ℤ)) := by
    rw [show x + (N : ℤ) - j = (x - j) + (N : ℤ) by ring, Int.add_emod, hNm]
  rw [hkey]
  set a : ℤ := (x - j) % (2 * (N : ℤ)) with ha
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by omega)
  have ham : a < 2 * (N : ℤ) := Int.emod_lt_of_pos _ hm
  rw [if_congr (paperG_half_test N hN ha0 ham) rfl rfl]
  by_cases h : a < (N : ℤ) <;> simp [h]

/-- The query-position period of `paperG` is `2 * N` for positive `N`. -/
theorem paperG_period (N : ℕ) (hN : 0 < N) (j x : ℤ) :
    paperG N j (x + 2 * (N : ℤ)) = paperG N j x := by
  unfold paperG
  push_cast
  have hkey : (x + 2 * (N : ℤ) - j) % (2 * (N : ℤ)) = (x - j) % (2 * (N : ℤ)) := by
    rw [show x + 2 * (N : ℤ) - j = (x - j) + (2 * (N : ℤ)) * 1 by ring]
    exact Int.add_mul_emod_self_left _ _ _
  rw [hkey]

/-- Translating the threshold by `l` is equivalent to translating the query position by `−l`
[ChildsLandahlParrilo2007]. -/
theorem paperG_shift (N : ℕ) (j x l : ℤ) :
    paperG N (j + l) x = paperG N j (x - l) := by
  unfold paperG
  rw [show x - (j + l) = x - l - j by ring]

/-- On doubled finite indices, `paperG` equals 1 when `ospBit` is true and −1 otherwise
[ChildsLandahlParrilo2007]. -/
theorem paperG_eq_ospBit (N : ℕ) [NeZero N] (hN : 0 < N) (j x : Fin (2 * N)) :
    paperG N (j : ℤ) (x : ℤ) =
      (if Qatlib.Concepts.OrderedOracle.TiSdpBridge.ospBit N j x then 1 else -1) := by
  unfold paperG Qatlib.Concepts.OrderedOracle.TiSdpBridge.ospBit
  by_cases h : ((x : ℤ) - (j : ℤ)) % ((2 * N : ℕ) : ℤ) < (N : ℤ)
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h)]

end Qatlib.Papers.OrderedSearch06.OracleSymmetry
