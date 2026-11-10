/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.MachineDefs
set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

theorem lemma6_amplification_identity (p : ℝ) (f : ℕ) :
    p + ∑ j ∈ Finset.range f, p * (1 - 2 * p) ^ (2 * j) * (2 - 2 * p) ^ 2 =
      1 - (1 - p) * (1 - 2 * p) ^ (2 * f) := by
  induction f with
  | zero =>
    rw [Finset.sum_range_zero, pow_zero]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : p + (∑ j ∈ Finset.range n,
          p * (1 - 2 * p) ^ (2 * j) * (2 - 2 * p) ^ 2 +
          p * (1 - 2 * p) ^ (2 * n) * (2 - 2 * p) ^ 2) =
        (1 - (1 - p) * (1 - 2 * p) ^ (2 * n)) +
          p * (1 - 2 * p) ^ (2 * n) * (2 - 2 * p) ^ 2 := by
      rw [← add_assoc, ih]
    rw [hstep]
    have hpow : (1 - 2 * p) ^ (2 * (n + 1)) =
        (1 - 2 * p) ^ (2 * n) * (1 - 2 * p) ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    rw [hpow]
    ring

theorem lemma6_amplified_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℕ) :
    0 ≤ 1 - (1 - p) * (1 - 2 * p) ^ (2 * f) ∧
      1 - (1 - p) * (1 - 2 * p) ^ (2 * f) ≤ 1 := by
  have ha0 : 0 ≤ 1 - p := by linarith
  have ha1 : 1 - p ≤ 1 := by linarith
  have hb4 : (1 - 2 * p) ^ 2 ≤ 1 := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 - 2 * p))
      (by linarith : (0 : ℝ) ≤ 1 + (1 - 2 * p))
    nlinarith [h]
  have hbpow_eq : (1 - 2 * p) ^ (2 * f) = ((1 - 2 * p) ^ 2) ^ f := by rw [pow_mul]
  have hbpow_nonneg : 0 ≤ (1 - 2 * p) ^ (2 * f) := by
    rw [hbpow_eq]
    exact pow_nonneg (sq_nonneg _) _
  have hbpow_le : (1 - 2 * p) ^ (2 * f) ≤ 1 := by
    rw [hbpow_eq]
    exact pow_le_one₀ (sq_nonneg _) hb4
  have hprod0 : 0 ≤ (1 - p) * (1 - 2 * p) ^ (2 * f) := mul_nonneg ha0 hbpow_nonneg
  have hprod1 : (1 - p) * (1 - 2 * p) ^ (2 * f) ≤ 1 := by
    calc (1 - p) * (1 - 2 * p) ^ (2 * f) ≤ 1 * 1 :=
          mul_le_mul ha1 hbpow_le hbpow_nonneg (by norm_num)
      _ = 1 := by ring
  exact ⟨by linarith, by linarith⟩

theorem lemma6_amplified_machine (M : QTM) (hlog : LogSpace M) (hsteps : PolyTime M)
    (f : ℕ → ℕ) (hf : PolyBounded f) :
    ∃ Mf : QTM,
      LogSpace Mf ∧ PolyTime Mf ∧
        ∀ x : List Bool, Mf.acceptProb x =
          1 - (1 - M.acceptProb x) * (1 - 2 * M.acceptProb x) ^ (2 * f x.length) := by
  obtain ⟨c1, hc1⟩ := hf
  obtain ⟨c2, hc2⟩ := hsteps
  refine ⟨{ space := M.space
            steps := fun n => (2 * f n + 1) * M.steps n
            acceptProb := fun x =>
              1 - (1 - M.acceptProb x) * (1 - 2 * M.acceptProb x) ^ (2 * f x.length)
            acceptProb_nonneg := fun x =>
              (lemma6_amplified_bounds (M.acceptProb x) (M.acceptProb_nonneg x)
                (M.acceptProb_le_one x) (f x.length)).1
            acceptProb_le_one := fun x =>
              (lemma6_amplified_bounds (M.acceptProb x) (M.acceptProb_nonneg x)
                (M.acceptProb_le_one x) (f x.length)).2 }, ?_, ?_, ?_⟩
  · simpa [LogSpace] using hlog
  · refine ⟨c1 + c2 + 2, fun n => ?_⟩
    have h1 : f n ≤ (n + 2) ^ c1 := hc1 n
    have h2 : M.steps n ≤ (n + 2) ^ c2 := hc2 n
    have hn2 : 2 ≤ n + 2 := by omega
    have hbase : 1 ≤ (n + 2) ^ c1 := by
      have hpos : 0 < (n + 2) ^ c1 := pow_pos (by omega : (0 : ℕ) < n + 2) c1
      omega
    have h2f : 2 * f n + 1 ≤ 3 * (n + 2) ^ c1 := by
      have hmul : 2 * f n ≤ 2 * (n + 2) ^ c1 := Nat.mul_le_mul_left 2 h1
      omega
    have h3 : 3 ≤ (n + 2) ^ 2 := by
      have h := Nat.mul_le_mul hn2 hn2
      calc 3 ≤ 2 * 2 := by norm_num
        _ ≤ (n + 2) * (n + 2) := h
        _ = (n + 2) ^ 2 := by ring
    calc (2 * f n + 1) * M.steps n
        ≤ (3 * (n + 2) ^ c1) * (n + 2) ^ c2 := Nat.mul_le_mul h2f h2
      _ = 3 * ((n + 2) ^ c1 * (n + 2) ^ c2) := by ring
      _ ≤ (n + 2) ^ 2 * ((n + 2) ^ c1 * (n + 2) ^ c2) :=
          Nat.mul_le_mul_right _ h3
      _ = (n + 2) ^ (c1 + c2 + 2) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
  · intro x
    rfl

end

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
