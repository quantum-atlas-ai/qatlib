/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Circuit
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor42

theorem corollary4_2_ratio_separation
    (p a b : ℝ) (hp : 0 < p) (happ : |a - b| < 1 / (3 * p)) :
    (2 ≤ p * a → 3 / 2 < p * b) ∧ (p * a ≤ 1 → p * b < 3 / 2) := by
  have hkey : p * (1 / (3 * p)) = 1 / 3 := by
    field_simp
  obtain ⟨hlow, hhigh⟩ := abs_lt.1 happ
  constructor
  · intro ha
    have h1 : -(1 / 3) < p * (a - b) := by
      have h := mul_lt_mul_of_pos_left hlow hp
      rwa [mul_neg, hkey] at h
    have hsub : p * (a - b) = p * a - p * b := by ring
    nlinarith
  · intro ha
    have h1 : p * (a - b) < 1 / 3 := by
      have h := mul_lt_mul_of_pos_left hhigh hp
      rwa [hkey] at h
    have hsub : p * (a - b) = p * a - p * b := by ring
    nlinarith

theorem corollary4_2_decides
    (p a b : ℝ) (hp : 0 < p) (happ : |a - b| < 1 / (3 * p))
    (hpromise : 2 ≤ p * a ∨ p * a ≤ 1) :
    (3 / 2 < p * b ∧ 2 ≤ p * a) ∨ (p * b < 3 / 2 ∧ p * a ≤ 1) := by
  obtain ⟨hyes, hno⟩ := corollary4_2_ratio_separation p a b hp happ
  rcases hpromise with h | h
  · exact Or.inl ⟨hyes h, h⟩
  · exact Or.inr ⟨hno h, h⟩

theorem corollary4_2_branches_disjoint (p a : ℝ) :
    ¬(2 ≤ p * a ∧ p * a ≤ 1) := by
  intro ⟨h1, h2⟩
  linarith

end Qatlib.Papers.TensorNetwork08.MainResults.Cor42
