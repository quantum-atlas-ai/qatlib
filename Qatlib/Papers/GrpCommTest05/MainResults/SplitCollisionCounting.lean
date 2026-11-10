/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

theorem injective_comp_perm {k : ℕ} (F : Fin k → Fin k) (e : Equiv.Perm (Fin k)) :
    Function.Injective (F ∘ e) ↔ Function.Injective F := by
  constructor
  · intro h x y hxy
    have h' : (F ∘ e) (e.symm x) = (F ∘ e) (e.symm y) := by
      simpa [Function.comp] using hxy
    exact e.symm.injective (h h')
  · intro h x y hxy
    exact e.injective (h (by simpa [Function.comp] using hxy))

theorem collision_comp_perm {k : ℕ} (F : Fin k → Fin k) (e : Equiv.Perm (Fin k))
    {x y : Fin k} (hxy : x ≠ y) (hF : F x = F y) :
    e.symm x ≠ e.symm y ∧ (F ∘ e) (e.symm x) = (F ∘ e) (e.symm y) := by
  constructor
  · intro h
    exact hxy (e.symm.injective h)
  · simp [Function.comp, hF]

theorem split_pair_ratio (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℚ) ^ 2) / ((2 * (m : ℚ)) * (2 * (m : ℚ) - 1)) =
      (m : ℚ) / (2 * (m : ℚ) - 1) := by
  have hden : (2 * (m : ℚ) - 1) ≠ 0 := by
    have : (0 : ℚ) ≤ (m : ℚ) := by positivity
    intro h
    have : (2 * (m : ℚ)) = 1 := by linarith
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have hmq : (m : ℚ) ≠ 0 := by
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp

theorem split_prob_ge_half (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) / 2 ≤ (m : ℚ) / (2 * (m : ℚ) - 1) := by
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℚ) < 2 * (m : ℚ) - 1 := by linarith
  rw [le_div_iff₀ hden]
  linarith

theorem two_perm_fail_le_quarter {q : ℚ} (hq : (1 : ℚ) / 2 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ 2 ≤ (1 : ℚ) / 4 := by
  have hle : 1 - q ≤ (1 : ℚ) / 2 := by linarith
  have hnn : (0 : ℚ) ≤ 1 - q := by linarith
  have hmul := mul_le_mul hle hle hnn (by norm_num : (0 : ℚ) ≤ 1 / 2)
  nlinarith

theorem amplification_error_bounds {gamma : ℝ} (hgamma : gamma < 1 / 4) :
    (1 : ℝ) / 4 + gamma < 1 / 2 ∧ (3 : ℝ) / 8 ≤ (1 - gamma) / 2 := by
  constructor <;> linarith

end Qatlib.Papers.GrpCommTest05.MainResults
