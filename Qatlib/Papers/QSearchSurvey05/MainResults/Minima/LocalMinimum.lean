/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max

/-!
# Local minima on the Boolean cube

This module proves existence and elementary descent properties of local minima on the Boolean
cube. The theorem `theorem32_local_minimum` balances the scalar query expression used in the
local minimum application of [Ambainis2005], obtaining twice 2^(n/3)n^(1/6).

## Main statements

* `localMin_exists`: Proves that every integer valued function on the Boolean cube has a local
  minimum.
* `theorem32_local_minimum`: Exhibits a positive memory parameter with the stated scalar query
  bound.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- Every integer valued function on the n dimensional Boolean cube has a local minimum. See
[Ambainis2005]. -/
theorem localMin_exists (n : ℕ) (f : (Fin n → Bool) → ℤ) :
    ∃ x : Fin n → Bool, IsLocalMinimum f x := by
  have hne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨x, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n → Bool)) f hne
  exact ⟨x, fun i => hmin _ (Finset.mem_univ _)⟩

/-- A Boolean string is a local minimum exactly when no single bit flip strictly decreases the
objective. See [Ambainis2005]. -/
theorem localMin_iff_no_improvement (n : ℕ) (f : (Fin n → Bool) → ℤ) (x : Fin n → Bool) :
    IsLocalMinimum f x ↔
      ¬ ∃ i : Fin n, f (Function.update x i (Bool.not (x i))) < f x := by
  unfold IsLocalMinimum
  constructor
  · rintro h ⟨i, hi⟩
    exact absurd hi (not_lt.mpr (h i))
  · intro h i
    by_contra hlt
    exact h ⟨i, not_le.mp hlt⟩

/-- A Boolean string that is not a local minimum has a bit flip that strictly decreases the
objective. See [Ambainis2005]. -/
theorem localMin_descent_step (n : ℕ) (f : (Fin n → Bool) → ℤ) (x : Fin n → Bool) :
    ¬ IsLocalMinimum f x →
      ∃ i : Fin n, f (Function.update x i (Bool.not (x i))) < f x := by
  intro hx
  by_contra hall
  exact hx ((localMin_iff_no_improvement n f x).mpr hall)

/-- A sequence of L Boolean strings with pairwise distinct objective values has length at most
2^n. See [Ambainis2005]. -/
theorem localMin_descent_length (n L : ℕ) (f : (Fin n → Bool) → ℤ)
    (x : Fin L → (Fin n → Bool)) (hval : Function.Injective fun i => f (x i)) :
    L ≤ 2 ^ n := by
  have hx : Function.Injective x :=
    fun a b hab => hval (by show f (x a) = f (x b); rw [hab])
  have hcard : L ≤ Fintype.card (Fin n → Bool) := by
    simpa using Fintype.card_le_of_injective x hx
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  exact hcard

/-- For positive n, the square root of `LocalMinOptimalMemory` n is 2^(n/3)n^(1/6). -/
theorem localMin_ledger_sqrt (n : ℕ) (hn : 0 < n) :
    Real.sqrt (LocalMinOptimalMemory n) =
      (2 : ℝ) ^ ((1 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : LocalMinOptimalMemory n =
      ((2 : ℝ) ^ ((1 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by
    unfold LocalMinOptimalMemory
    rw [mul_pow]
    have e1 : ((2 : ℝ) ^ ((1 : ℝ) / 3 * (n : ℝ))) ^ 2 =
        (2 : ℝ) ^ ((2 : ℝ) / 3 * (n : ℝ)) := by
      rw [sq, ← Real.rpow_add h2]
      congr 1
      ring
    have e2 : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 = (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [sq, ← Real.rpow_add hnpos]
      congr 1
      ring
    rw [e1, e2]
  rw [hsq]
  exact Real.sqrt_sq (le_of_lt (mul_pos
    (Real.rpow_pos_of_pos h2 _) (Real.rpow_pos_of_pos hnpos _)))

/-- For positive n, dividing 2^n√n by `LocalMinOptimalMemory` n gives 2^(n/3)n^(1/6). -/
theorem localMin_ledger_ratio (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ (n : ℝ) * Real.sqrt (n : ℝ) / LocalMinOptimalMemory n =
      (2 : ℝ) ^ ((1 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : (2 : ℝ) ^ (n : ℝ) * Real.sqrt (n : ℝ) / LocalMinOptimalMemory n =
      ((2 : ℝ) ^ (n : ℝ) / (2 : ℝ) ^ ((2 : ℝ) / 3 * (n : ℝ))) *
        ((n : ℝ) ^ ((1 : ℝ) / 2) / (n : ℝ) ^ ((1 : ℝ) / 3)) := by
    unfold LocalMinOptimalMemory
    rw [Real.sqrt_eq_rpow]
    field_simp
  rw [hsplit, ← Real.rpow_sub h2, ← Real.rpow_sub hnpos]
  have e1 : (n : ℝ) - (2 : ℝ) / 3 * (n : ℝ) = (1 : ℝ) / 3 * (n : ℝ) := by ring
  have e2 : (1 : ℝ) / 2 - (1 : ℝ) / 3 = (1 : ℝ) / 6 := by norm_num
  rw [e1, e2]

/-- For n ≥ 1, there is a positive memory parameter whose scalar local minimum query expression
is at most twice 2^(n/3)n^(1/6). See [Ambainis2005]. -/
theorem theorem32_local_minimum (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℝ, 0 < m ∧
      LocalMinQueryLedger n m ≤
        2 * ((2 : ℝ) ^ ((1 : ℝ) / 3 * (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
  have hn0 : 0 < n := hn
  refine ⟨LocalMinOptimalMemory n, ?_, ?_⟩
  · unfold LocalMinOptimalMemory
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    exact mul_pos (Real.rpow_pos_of_pos h2 _) (Real.rpow_pos_of_pos hnpos _)
  · unfold LocalMinQueryLedger
    rw [← Real.rpow_natCast]
    rw [localMin_ledger_sqrt n hn0, localMin_ledger_ratio n hn0]
    linarith

end Qatlib.Papers.QSearchSurvey05.MainResults
