/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

open Finset

namespace Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity

lemma sub_two_add_one {r : ℕ} (hr : 2 ≤ r) : r - 2 + 1 = r - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [Nat.add_comm]

lemma le_r_sub_one_of_le_sub_two {a r : ℕ} (h : a ≤ r - 2) : a ≤ r - 1 :=
  le_trans h (Nat.sub_le_sub_left (by norm_num : 1 ≤ 2) r)

lemma succ_le_r_sub_one {a s r : ℕ} (ha : a ≤ s) (h : s ≤ r - 2) (hr : 2 ≤ r) :
    a + 1 ≤ r - 1 := by
  have h1 : a ≤ r - 2 := le_trans ha h
  have h2 : a + 1 ≤ r - 2 + 1 := Nat.succ_le_succ h1
  simpa [sub_two_add_one hr] using h2

def quantumInt (r n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi / (r : ℝ)) / Real.sin (Real.pi / (r : ℝ))

def DeltaRoot (r n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * quantumInt r (n + 1)

def qfac (r n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, quantumInt r (i + 1)

def ThetaHat (r m n p : ℕ) : ℝ :=
  qfac r (m + n + p + 1) * qfac r n * qfac r m * qfac r p /
    (qfac r (m + n) * qfac r (n + p) * qfac r (p + m))

def vertexFactor (r m n p : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt
    (DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p) /
      ThetaHat r m n p))

theorem quantumInt_pos {r n : ℕ} (hr : 2 ≤ r) (hn0 : 1 ≤ n) (hnr : n ≤ r - 1) :
    0 < quantumInt r n := by
  have hrR : (0 : ℝ) < (r : ℝ) := by positivity
  have hden : 0 < Real.sin (Real.pi / (r : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hrR]
      have h : 0 < Real.pi * ((r : ℝ) - 1) :=
        mul_pos Real.pi_pos (by linarith [show (2 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr])
      nlinarith [h]
  have hnum : 0 < Real.sin ((n : ℝ) * Real.pi / (r : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hrR]
      have hnR : (n : ℝ) ≤ (r : ℝ) - 1 := by
        have h1 : ((n : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hnr
        have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          have : 1 ≤ r := le_trans (by norm_num) hr
          push_cast [this]
          ring
        linarith [h1, hr1]
      have h : 0 < Real.pi * ((r : ℝ) - n) :=
        mul_pos Real.pi_pos (by linarith)
      nlinarith [h]
  exact div_pos hnum hden

theorem quantumInt_self_eq_zero {r : ℕ} (hr : 0 < r) : quantumInt r r = 0 := by
  unfold quantumInt
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h : (r : ℝ) * Real.pi / (r : ℝ) = Real.pi := by field_simp
  rw [h, Real.sin_pi]
  simp

theorem qfac_pos {r n : ℕ} (hr : 2 ≤ r) (hn : n ≤ r - 1) : 0 < qfac r n := by
  unfold qfac
  apply Finset.prod_pos
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hi1 : i + 1 ≤ n := Nat.succ_le_of_lt hi'
  exact quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le i)) (le_trans hi1 hn)

theorem ThetaHat_pos {r m n p : ℕ} (hr : 2 ≤ r) (h : m + n + p ≤ r - 2) :
    0 < ThetaHat r m n p := by
  unfold ThetaHat
  have hm_le : m ≤ m + n + p := by
    have h1 : m ≤ m + n := Nat.le_add_right m n
    exact le_trans h1 (Nat.le_add_right (m + n) p)
  have hn_le : n ≤ m + n + p := by
    have h1 : n ≤ m + n := Nat.le_add_left n m
    exact le_trans h1 (Nat.le_add_right (m + n) p)
  have hp_le : p ≤ m + n + p := by
    have h1 : p ≤ n + p := Nat.le_add_left p n
    have h2 : n + p ≤ m + n + p := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (n + p) m
    exact le_trans h1 h2
  have hmn_le : m + n ≤ m + n + p := Nat.le_add_right (m + n) p
  have hnp_le : n + p ≤ m + n + p := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (n + p) m
  have hpm_le : p + m ≤ m + n + p := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (p + m) n
  have hsum_le : m + n + p ≤ r - 1 := le_r_sub_one_of_le_sub_two h
  have h1 : 0 < qfac r (m + n + p + 1) := by
    apply qfac_pos hr
    have hs : m + n + p + 1 ≤ r - 2 + 1 := Nat.succ_le_succ h
    simpa [sub_two_add_one hr] using hs
  have h2 : 0 < qfac r n := qfac_pos hr (le_trans hn_le hsum_le)
  have h3 : 0 < qfac r m := qfac_pos hr (le_trans hm_le hsum_le)
  have h4 : 0 < qfac r p := qfac_pos hr (le_trans hp_le hsum_le)
  have h5 : 0 < qfac r (m + n) := qfac_pos hr (le_trans hmn_le hsum_le)
  have h6 : 0 < qfac r (n + p) := qfac_pos hr (le_trans hnp_le hsum_le)
  have h7 : 0 < qfac r (p + m) := qfac_pos hr (le_trans hpm_le hsum_le)
  positivity

theorem DeltaRoot_prod_eq {r m n p : ℕ} :
    DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p)
      = quantumInt r (m + p + 1) * quantumInt r (m + n + 1)
          * quantumInt r (n + p + 1) := by
  have hsign : ((-1 : ℝ) ^ (m + p)) * ((-1 : ℝ) ^ (m + n)) * ((-1 : ℝ) ^ (n + p))
      = 1 := by
    rw [← pow_add, ← pow_add]
    have hsum : m + p + (m + n) + (n + p) = 2 * (m + n + p) := by ring
    rw [hsum, pow_mul]
    norm_num
  unfold DeltaRoot
  rw [show ((-1 : ℝ) ^ (m + p) * quantumInt r (m + p + 1))
        * ((-1 : ℝ) ^ (m + n) * quantumInt r (m + n + 1))
        * ((-1 : ℝ) ^ (n + p) * quantumInt r (n + p + 1))
      = (((-1 : ℝ) ^ (m + p)) * ((-1 : ℝ) ^ (m + n)) * ((-1 : ℝ) ^ (n + p)))
        * (quantumInt r (m + p + 1) * quantumInt r (m + n + 1)
            * quantumInt r (n + p + 1)) by ring]
  rw [hsign, one_mul]

theorem vertexFactor_pos {r m n p : ℕ} (hr : 2 ≤ r) (h : m + n + p ≤ r - 2) :
    0 < vertexFactor r m n p := by
  unfold vertexFactor
  have hmp_le : m + p ≤ m + n + p := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (m + p) n
  have hmn_le : m + n ≤ m + n + p := Nat.le_add_right (m + n) p
  have hnp_le : n + p ≤ m + n + p := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (n + p) m
  have hq : 0 < DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p)
      / ThetaHat r m n p := by
    rw [DeltaRoot_prod_eq]
    have h1 : 0 < quantumInt r (m + p + 1) :=
      quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hmp_le h hr)
    have h2 : 0 < quantumInt r (m + n + 1) :=
      quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hmn_le h hr)
    have h3 : 0 < quantumInt r (n + p + 1) :=
      quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hnp_le h hr)
    exact div_pos (by positivity) (ThetaHat_pos hr h)
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hq)

theorem vertexFactor_pow_four {r m n p : ℕ} (hr : 2 ≤ r) (h : m + n + p ≤ r - 2) :
    vertexFactor r m n p ^ 4
      = DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p)
          / ThetaHat r m n p := by
  have hq : 0 ≤ DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p)
      / ThetaHat r m n p := by
    have hmp_le : m + p ≤ m + n + p := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (m + p) n
    have hmn_le : m + n ≤ m + n + p := Nat.le_add_right (m + n) p
    have hnp_le : n + p ≤ m + n + p := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.le_add_right (n + p) m
    have hpos : 0 < DeltaRoot r (m + p) * DeltaRoot r (m + n) * DeltaRoot r (n + p)
        / ThetaHat r m n p := by
      rw [DeltaRoot_prod_eq]
      have h1 : 0 < quantumInt r (m + p + 1) :=
        quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hmp_le h hr)
      have h2 : 0 < quantumInt r (m + n + 1) :=
        quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hmn_le h hr)
      have h3 : 0 < quantumInt r (n + p + 1) :=
        quantumInt_pos hr (Nat.succ_le_succ (Nat.zero_le _)) (succ_le_r_sub_one hnp_le h hr)
      exact div_pos (by positivity) (ThetaHat_pos hr h)
    exact le_of_lt hpos
  unfold vertexFactor
  have hs : 0 ≤ Real.sqrt (DeltaRoot r (m + p) * DeltaRoot r (m + n)
      * DeltaRoot r (n + p) / ThetaHat r m n p) := Real.sqrt_nonneg _
  rw [show Real.sqrt (Real.sqrt (DeltaRoot r (m + p) * DeltaRoot r (m + n)
        * DeltaRoot r (n + p) / ThetaHat r m n p)) ^ 4
      = (Real.sqrt (Real.sqrt (DeltaRoot r (m + p) * DeltaRoot r (m + n)
          * DeltaRoot r (n + p) / ThetaHat r m n p)) ^ 2) ^ 2 by ring]
  rw [Real.sq_sqrt hs, Real.sq_sqrt hq]

theorem vertexFactor_pow_four_quantumInt {r m n p : ℕ} (hr : 2 ≤ r)
    (h : m + n + p ≤ r - 2) :
    vertexFactor r m n p ^ 4
      = quantumInt r (m + p + 1) * quantumInt r (m + n + 1)
          * quantumInt r (n + p + 1) / ThetaHat r m n p := by
  rw [vertexFactor_pow_four hr h, DeltaRoot_prod_eq]

end Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity
