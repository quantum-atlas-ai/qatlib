/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Quantitative core of Theorem 1 of Ettinger–Høyer–Knill,
"The quantum query complexity of the hidden subgroup problem is polynomial".

This file records the finite-group counting and query-count arithmetic that
underlies the algorithm's `O(log^4 |G|)` oracle-call bound.
-/
import Qatlib.Papers.EttingerHSP04.MainResults.SubgroupCounting
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Minimal
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.EttingerHSP04.MainResults

open Qatlib.Papers.EttingerHSP04.MainResults

open scoped BigOperators

/-! ### Adjoining one generator doubles a subgroup -/

/-- `s = 2 log₂(4r³)` oracle calls per `ExactTest`, and at most `log₂ r + 1`
binary-search rounds, give the exact algorithm's query count. -/
noncomputable def exactQueryCount (r : Nat) : Nat :=
  (2 * (4 * r ^ 3).log2) * (r.log2 + 1)

/-- The exact algorithm makes only `O(log^4 |G|)` oracle calls. -/
theorem exactQueryCount_le {G : Type*} [Group G] [Fintype G] :
    exactQueryCount (Fintype.card (Subgroup G)) ≤
      64 * ((Fintype.card G).log2 + 1) ^ 4 := by
  classical
  set N := Fintype.card G with hN
  set m := N.log2 with hm
  set B := (m + 1) * (m + 2) with hBdef
  set r := Fintype.card (Subgroup G) with hrdef
  have hrB : r ≤ 2 ^ B := by
    have h := card_subgroups_le_two_pow (G := G)
    simpa only [hN, hm, hBdef, hrdef] using h
  have hrne : r ≠ 0 := by
    rw [hrdef]
    exact Fintype.card_ne_zero (α := Subgroup G)
  have hlogr : r.log2 ≤ B := by
    have hltB : r.log2 < B + 1 :=
      (Nat.log2_lt hrne).mpr
        (lt_of_le_of_lt hrB (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)))
    omega
  have hr3 : r ^ 3 ≤ 2 ^ (3 * B) := by
    calc r ^ 3 ≤ (2 ^ B) ^ 3 := Nat.pow_le_pow_left hrB 3
      _ = 2 ^ (B * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * B) := by rw [Nat.mul_comm]
  have hlt : 4 * r ^ 3 < 2 ^ (3 * B + 3) := by
    have h4 : 4 * r ^ 3 ≤ 4 * 2 ^ (3 * B) := Nat.mul_le_mul_left 4 hr3
    have h4' : 4 * 2 ^ (3 * B) = 2 ^ (3 * B + 2) := by
      calc 4 * 2 ^ (3 * B) = 2 ^ 2 * 2 ^ (3 * B) := by norm_num
        _ = 2 ^ (2 + 3 * B) := by rw [← pow_add]
        _ = 2 ^ (3 * B + 2) := by rw [Nat.add_comm]
    rw [h4'] at h4
    exact lt_of_le_of_lt h4 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hlog4 : (4 * r ^ 3).log2 ≤ 3 * B + 2 := by
    have h := (Nat.log2_lt (n := 4 * r ^ 3)
      (Nat.mul_ne_zero (by norm_num) (pow_ne_zero 3 hrne))).mpr hlt
    omega
  have hs : exactQueryCount r ≤ (6 * B + 4) * (B + 1) := by
    unfold exactQueryCount
    have h1 : 2 * (4 * r ^ 3).log2 ≤ 2 * (3 * B + 2) := Nat.mul_le_mul_left 2 hlog4
    have h2 : r.log2 + 1 ≤ B + 1 := Nat.add_le_add_right hlogr 1
    exact Nat.mul_le_mul (by omega) h2
  have hB : B ≤ 2 * (m + 1) ^ 2 := by
    rw [hBdef]
    nlinarith
  have hfinal : (6 * B + 4) * (B + 1) ≤ 64 * (m + 1) ^ 4 := by
    nlinarith [hB]
  exact hs.trans hfinal

/-- Binary search over `r` candidates needs at most `log₂ r + 1` comparison rounds. -/
theorem binary_search_depth (r : Nat) : ∃ k ≤ r.log2 + 1, r ≤ 2 ^ k :=
  ⟨r.log2 + 1, le_rfl, le_of_lt Nat.lt_log2_self⟩

end Qatlib.Papers.EttingerHSP04.MainResults
