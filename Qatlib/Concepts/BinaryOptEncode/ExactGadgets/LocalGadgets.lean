/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
namespace Qatlib.Concepts.BinaryOptEncode.ExactGadgets

def signPlus (s : ℤ) : ℤ := if 0 ≤ s then 1 else -1

theorem sign_constraints_iff (s a : ℤ) (ha : a = 1 ∨ a = -1) :
    (∃ r t : ℤ, 0 ≤ r ∧ 0 ≤ t ∧ a * s = r ∧ a + 2 * r = 1 + t) ↔
      a = signPlus s := by
  constructor
  · rintro ⟨r, t, hr, ht, hprod, hsum⟩
    rcases ha with h | h <;> subst a
    · have hs : 0 ≤ s := by nlinarith
      simp [signPlus, hs]
    · have hs : ¬0 ≤ s := by intro hs; nlinarith
      simp [signPlus, hs]
  · intro hsign
    by_cases hs : 0 ≤ s
    · have h : a = 1 := by simpa [signPlus, hs] using hsign
      rw [h]
      exact ⟨s, 2 * s, hs, by omega, by ring, by ring⟩
    · have h : a = -1 := by simpa [signPlus, hs] using hsign
      rw [h]
      exact ⟨-s, -2 * s - 2, by omega, by omega, by ring, by ring⟩

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def rosenberg (u w v : Bool) : ℝ :=
  3 * bitValue v + bitValue u * bitValue w -
    2 * bitValue u * bitValue v - 2 * bitValue w * bitValue v

theorem rosenberg_exact (u w v : Bool) :
    0 ≤ rosenberg u w v ∧
      (rosenberg u w v = 0 ↔ v = (u && w)) ∧
      (v ≠ (u && w) → 1 ≤ rosenberg u w v) := by
  cases u <;> cases w <;> cases v <;> norm_num [rosenberg, bitValue]

theorem rosenberg_substitution (u w v : Bool) (q p penalty : ℝ)
    (hpenalty : |p| < penalty) :
    q + p * (bitValue u * bitValue w) ≤ q + p * bitValue v + penalty * rosenberg u w v ∧
      (q + p * (bitValue u * bitValue w) = q + p * bitValue v + penalty * rosenberg u w v ↔
        v = (u && w)) := by
  cases u <;> cases w <;> cases v <;> norm_num [rosenberg, bitValue]
  all_goals constructor <;> nlinarith [le_abs_self p, neg_le_abs p]

theorem selector_abs (s t : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    t * s = |s| := by
  rcases ht with rfl | rfl
  · simp only [one_mul] at h ⊢
    exact (abs_of_nonneg h).symm
  · have hs : s ≤ 0 := by linarith
    simpa using (abs_of_nonpos hs).symm

theorem selector_relu (s t : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    (t * s + s) / 2 = max 0 s := by
  rw [selector_abs s t ht h]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, max_eq_right hs]
    ring
  · rw [abs_of_neg (lt_of_not_ge hs), max_eq_left (le_of_not_ge hs)]
    ring

theorem selector_prelu (s t alpha : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    ((1 - alpha) * t + (1 + alpha)) * s / 2 =
      if 0 ≤ s then s else alpha * s := by
  have ha := selector_abs s t ht h
  calc
    ((1 - alpha) * t + (1 + alpha)) * s / 2 =
        ((1 - alpha) * (t * s) + (1 + alpha) * s) / 2 := by ring
    _ = ((1 - alpha) * |s| + (1 + alpha) * s) / 2 := by rw [ha]
    _ = if 0 ≤ s then s else alpha * s := by
      split_ifs with hs
      · rw [abs_of_nonneg hs]
        ring
      · rw [abs_of_neg (lt_of_not_ge hs)]
        ring

theorem selector_hinge (y output t : ℝ) (ht : t = 1 ∨ t = -1)
    (h : 0 ≤ t * (1 - y * output)) :
    (t * (1 - y * output) + 1 - y * output) / 2 = max 0 (1 - y * output) := by
  convert selector_relu (1 - y * output) t ht h using 1
  ring

end Qatlib.Concepts.BinaryOptEncode.ExactGadgets
