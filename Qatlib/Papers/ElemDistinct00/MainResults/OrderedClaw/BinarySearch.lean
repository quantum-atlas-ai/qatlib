/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw

def bsearch (f : ℕ → ℤ) (y : ℤ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, lo, hi => if f lo = y then some lo else none
  | d + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if f mid = y then some mid
        else if f mid < y then bsearch f y d (mid + 1) hi
        else bsearch f y d lo mid
      else none

theorem bsearch_spec (f : ℕ → ℤ) (hmono : Monotone f) (y : ℤ) :
    ∀ d lo hi, hi - lo ≤ 2 ^ d →
      (∃ x, lo ≤ x ∧ x < hi ∧ f x = y) →
      ∃ x', bsearch f y d lo hi = some x' ∧ f x' = y := by
  intro d
  induction d with
  | zero =>
    intro lo hi hlen hex
    obtain ⟨x, hxlo, hxhi, hxy⟩ := hex
    have hxeq : x = lo := by omega
    have hflo : f lo = y := by rw [← hxeq]; exact hxy
    exact ⟨lo, by simp only [bsearch, hflo, if_true], hflo⟩
  | succ d ih =>
    intro lo hi hlen hex
    rw [bsearch]
    by_cases hlo : lo < hi
    · rw [if_pos hlo]
      (try dsimp only)
      set mid := (lo + hi) / 2 with hmid_def
      by_cases hfound : f mid = y
      · exact ⟨mid, by rw [if_pos hfound], hfound⟩
      · rw [if_neg hfound]
        by_cases hlt : f mid < y
        · rw [if_pos hlt]
          obtain ⟨x, hxlo, hxhi, hxy⟩ := hex
          have hxgt : mid < x := by
            by_contra hle
            push Not at hle
            have hle' : f x ≤ f mid := hmono hle
            rw [hxy] at hle'
            linarith
          have hlen' : hi - (mid + 1) ≤ 2 ^ d := by
            have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          exact ih (mid + 1) hi hlen' ⟨x, by omega, hxhi, hxy⟩
        · rw [if_neg hlt]
          obtain ⟨x, hxlo, hxhi, hxy⟩ := hex
          have hy_lt : y < f mid := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hfound)
          have hxlt : x < mid := by
            by_contra hge
            push Not at hge
            have hge' : f mid ≤ f x := hmono hge
            rw [hxy] at hge'
            linarith
          have hlen' : mid - lo ≤ 2 ^ d := by
            have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          exact ih lo mid hlen' ⟨x, hxlo, hxlt, hxy⟩
    · obtain ⟨x, hxlo, hxhi, _⟩ := hex
      exact absurd hlo (by omega)

theorem exists_bsearch_of_ordered {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℤ)
    (hmono : Monotone f) (y : ℤ) (hex : ∃ x, x < N ∧ f x = y) :
    ∃ x', bsearch f y (Nat.clog 2 N) 0 N = some x' ∧ f x' = y := by
  apply bsearch_spec f hmono y (Nat.clog 2 N) 0 N
  · have hp := Nat.le_pow_clog (show 1 < 2 by norm_num) N
    simpa using hp
  · obtain ⟨x, hx, hxy⟩ := hex
    exact ⟨x, Nat.zero_le _, hx, hxy⟩

def orderedClawUpperCost (M N : ℕ) : ℝ := Real.sqrt (M : ℝ) * (Nat.clog 2 N : ℝ)

theorem log_le_orderedDepth (N : ℕ) : Nat.log 2 N ≤ Nat.clog 2 N :=
  Nat.log_le_clog 2 N

end Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw
