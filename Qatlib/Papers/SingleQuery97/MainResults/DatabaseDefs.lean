/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs

open Finset

abbrev DbVec (n : ℕ) := Fin n → Bool

def bitVal (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitVal_false : bitVal false = 0 := rfl

@[simp] theorem bitVal_true : bitVal true = 1 := rfl

theorem bitVal_eq_zero_or_one (b : Bool) : bitVal b = 0 ∨ bitVal b = 1 := by
  cases b <;> simp

theorem bitVal_injective : Function.Injective bitVal := by
  intro a b h
  cases a <;> cases b <;> simp_all

def dot {n : ℕ} (x y : DbVec n) : ℕ := ∑ i, bitVal (x i) * bitVal (y i)

def weight {n : ℕ} (y : DbVec n) : ℕ := ∑ i, bitVal (y i)

def wedge {n : ℕ} (x y : DbVec n) : DbVec n := fun i => x i && y i

theorem bitVal_and (a b : Bool) : bitVal (a && b) = bitVal a * bitVal b := by
  cases a <;> cases b <;> rfl

theorem weight_wedge_eq_dot {n : ℕ} (x y : DbVec n) :
    weight (wedge x y) = dot x y := by
  simp [weight, dot, wedge, bitVal_and]

theorem dot_comm {n : ℕ} (x y : DbVec n) : dot x y = dot y x := by
  simp [dot, mul_comm]

theorem dot_eq_filter_card {n : ℕ} (x k : DbVec n) :
    dot x k = (Finset.univ.filter fun i => k i && x i).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  cases hk : k i <;> cases hx : x i <;> simp [bitVal]

def signOfParity (m : ℕ) : ℂ := if m % 2 = 0 then 1 else -1

@[simp] theorem signOfParity_zero : signOfParity 0 = 1 := by
  simp [signOfParity]

theorem signOfParity_add (a b : ℕ) :
    signOfParity (a + b) = signOfParity a * signOfParity b := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [signOfParity, Nat.add_mod, ha, hb]

theorem signOfParity_mod_of_dvd {m N : ℕ} (hN : 2 ∣ N) :
    signOfParity (m % N) = signOfParity m := by
  unfold signOfParity
  rw [Nat.mod_mod_of_dvd m hN]

theorem signOfParity_eq_one_iff {m : ℕ} : signOfParity m = 1 ↔ m % 2 = 0 := by
  unfold signOfParity
  split_ifs with h
  · simp [h]
  · constructor
    · intro hc
      norm_num at hc
    · intro hc
      exact absurd hc h

theorem signOfParity_eq_neg_one_iff {m : ℕ} : signOfParity m = -1 ↔ m % 2 = 1 := by
  unfold signOfParity
  split_ifs with h
  · constructor
    · intro hc
      norm_num at hc
    · intro hc
      omega
  · constructor
    · intro _
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · exact absurd hm h
      · exact hm
    · intro _
      rfl

theorem signOfParity_eq_iff {a b : ℕ} :
    signOfParity a = signOfParity b ↔ a % 2 = b % 2 := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [signOfParity, ha, hb]
  all_goals
    intro hc
    norm_num at hc

def nprime (n : ℕ) : ℕ := 2 * ((n + 2) / 2) - 1

def registerN (n : ℕ) : ℕ := nprime n + 1

theorem registerN_eq (n : ℕ) : registerN n = 2 * ((n + 2) / 2) := by
  have h1 : 1 ≤ (n + 2) / 2 := Nat.div_pos (by omega) (by omega)
  have h2 : 1 ≤ 2 * ((n + 2) / 2) := by omega
  unfold registerN nprime
  omega

theorem registerN_pos (n : ℕ) : 0 < registerN n := by
  rw [registerN_eq]
  omega

theorem registerN_ne_zero (n : ℕ) : registerN n ≠ 0 :=
  ne_of_gt (registerN_pos n)

instance registerNNeZero (n : ℕ) : NeZero (registerN n) :=
  ⟨registerN_ne_zero n⟩

theorem two_dvd_registerN (n : ℕ) : 2 ∣ registerN n := by
  rw [registerN_eq]
  exact ⟨(n + 2) / 2, rfl⟩

theorem n_lt_registerN (n : ℕ) : n < registerN n := by
  rw [registerN_eq]
  have : n + 2 ≤ 2 * ((n + 2) / 2) + 2 := by
    have := Nat.div_add_mod (n + 2) 2
    omega
  omega

theorem weight_le_length {n : ℕ} (y : DbVec n) : weight y ≤ n := by
  have h : ∑ i, bitVal (y i) ≤ ∑ _i : Fin n, 1 := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases bitVal_eq_zero_or_one (y i) with h | h <;> omega
  simpa [weight] using h

theorem weight_wedge_lt_registerN {n : ℕ} (x y : DbVec n) :
    weight (wedge x y) < registerN n := by
  have h := weight_le_length (wedge x y)
  have hN := n_lt_registerN n
  omega

theorem weight_mod_registerN_eq {n : ℕ} (x y : DbVec n) :
    weight (wedge x y) % registerN n = weight (wedge x y) :=
  Nat.mod_eq_of_lt (weight_wedge_lt_registerN x y)

theorem weight_mod_registerN_parity {n : ℕ} (x y : DbVec n) :
    (weight (wedge x y) % registerN n) % 2 = dot x y % 2 := by
  rw [weight_mod_registerN_eq, weight_wedge_eq_dot]

def unitVec {n : ℕ} (i : Fin n) : DbVec n := fun j => decide (j = i)

theorem wedge_unit {n : ℕ} (i : Fin n) (y : DbVec n) :
    wedge (unitVec i) y = fun j => if j = i then y j else false := by
  funext j
  by_cases h : j = i <;> simp [wedge, unitVec, h]

theorem weight_wedge_unit {n : ℕ} (i : Fin n) (y : DbVec n) :
    weight (wedge (unitVec i) y) = bitVal (y i) := by
  rw [weight, wedge_unit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem dot_unit {n : ℕ} (i : Fin n) (y : DbVec n) :
    dot (unitVec i) y = bitVal (y i) := by
  rw [← weight_wedge_eq_dot, weight_wedge_unit]

theorem weightMod_determines {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, weight (wedge x y) % registerN n = weight (wedge x y') % registerN n) :
    y = y' := by
  funext i
  have hi := h (unitVec i)
  rw [weight_mod_registerN_eq, weight_mod_registerN_eq,
    weight_wedge_unit, weight_wedge_unit] at hi
  exact bitVal_injective hi

theorem parity_answers_determine {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, dot x y = dot x y') : y = y' := by
  funext i
  have hi := h (unitVec i)
  rw [dot_unit, dot_unit] at hi
  exact bitVal_injective hi

theorem sign_answers_determine {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, signOfParity (dot x y) = signOfParity (dot x y')) : y = y' := by
  funext i
  have hi := h (unitVec i)
  rw [dot_unit, dot_unit] at hi
  have hp := (signOfParity_eq_iff (a := bitVal (y i)) (b := bitVal (y' i))).mp hi
  cases hy : y i <;> cases hy' : y' i <;> simp_all [bitVal]

end Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
