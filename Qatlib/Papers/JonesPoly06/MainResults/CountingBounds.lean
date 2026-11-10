/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPoly06.MainResults

section TemperleyLieb

variable {R : Type*} [CommRing R]

theorem SourceLemma51 {p : ℕ} (c : R) (e : Fin p → R) :
    (∏ i, (c * e i) = c ^ p * ∏ i, e i) ∧
    (∀ j : Fin p, e j = 0 → ∏ i, (c * e i) = 0) ∧
    ((∀ i, e i * e i = e i) → (∏ i, e i) * (∏ i, e i) = ∏ i, e i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · intro j hj
    have hzero : ∏ i, e i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [Finset.prod_mul_distrib, Finset.prod_const, hzero, mul_zero]
  · intro hidem
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hidem i]

end TemperleyLieb

theorem gap_decision (p z : ℝ) (_hp0 : 0 ≤ p) (_hp : p ≤ 1)
    (hz : |z - p| ≤ 1 / 8) (hpromise : 3 / 4 ≤ p ∨ p ≤ 1 / 4) :
    (1 / 2 ≤ z → 3 / 4 ≤ p) ∧ (z < 1 / 2 → p ≤ 1 / 4) := by
  rw [abs_le] at hz
  constructor
  · intro hz2
    rcases hpromise with h | h
    · exact h
    · linarith [hz.1, hz2]
  · intro hz2
    rcases hpromise with h | h
    · linarith [hz.2, hz2]
    · exact h

theorem gap_decision_strict (p z : ℝ) (_hp0 : 0 ≤ p) (_hp : p ≤ 1)
    (hz : |z - p| ≤ 1 / 8) (hpromise : 3 / 4 ≤ p ∨ p ≤ 1 / 4) :
    (1 / 2 < z → 3 / 4 ≤ p) ∧ (z ≤ 1 / 2 → p ≤ 1 / 4) := by
  rw [abs_le] at hz
  constructor
  · intro hz2
    rcases hpromise with h | h
    · exact h
    · linarith [hz.1, hz2]
  · intro hz2
    rcases hpromise with h | h
    · linarith [hz.2, hz2]
    · exact h

theorem msb_bits_extract (n N : ℕ) (_hN : N < 2 ^ n) (b : ℝ)
    (_hb0 : 0 ≤ b) (hb : |b - (N : ℝ) / 2 ^ n| < 1 / 2 ^ (n + 1)) :
    ⌊b * 2 ^ n + 1 / 2⌋ = (N : ℤ) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [abs_lt] at hb
  have hmul1 : -(1 / 2 : ℝ) < b * 2 ^ n - (N : ℝ) := by
    have h1 := mul_lt_mul_of_pos_right hb.1 h2n
    have hsimp : (b - (N : ℝ) / 2 ^ n) * 2 ^ n = b * 2 ^ n - (N : ℝ) := by
      field_simp
    rw [hsimp] at h1
    have hval : (1 / 2 ^ (n + 1) : ℝ) * 2 ^ n = 1 / 2 := by
      rw [pow_succ]
      field_simp
    linarith
  have hmul2 : b * 2 ^ n - (N : ℝ) < 1 / 2 := by
    have h1 := mul_lt_mul_of_pos_right hb.2 h2n
    have hsimp : (b - (N : ℝ) / 2 ^ n) * 2 ^ n = b * 2 ^ n - (N : ℝ) := by
      field_simp
    rw [hsimp] at h1
    have hval : (1 / 2 ^ (n + 1) : ℝ) * 2 ^ n = 1 / 2 := by
      rw [pow_succ]
      field_simp
    linarith
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem msb_threshold (n N : ℕ) (hn : 0 < n) (_hN : N < 2 ^ n) :
    (1 / 2 ≤ (N : ℝ) / 2 ^ n ↔ 2 ^ (n - 1) ≤ N) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [le_div_iff₀ h2n]
  have hhalf : (1 / 2 : ℝ) * 2 ^ n = ((2 ^ (n - 1) : ℕ) : ℝ) := by
    have hn' : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn', pow_succ]
    push_cast
    ring
  rw [hhalf, Nat.cast_le]

end Qatlib.Papers.JonesPoly06.MainResults
