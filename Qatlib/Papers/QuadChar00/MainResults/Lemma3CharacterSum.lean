/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs

/-!
# Quadratic character sums over finite fields

This module evaluates the sum of the finite field quadratic character. The two cases in
`lemma3_quadCharSum` distinguish characteristic two from all other characteristics. See
[VanDamHallgren2000].

## Main statements

* `lemma3_quadCharSum`: The quadratic character sums to zero when the characteristic is not two,
  and to the field cardinality minus one in characteristic two.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

/-- The quadratic character sums to zero when the characteristic is not two, and to the field
cardinality minus one in characteristic two. See [VanDamHallgren2000]. -/
theorem lemma3_quadCharSum (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    (ringChar F ≠ 2 → ∑ x : F, finiteFieldQuadChar F x = 0) ∧
    (ringChar F = 2 →
      ∑ x : F, finiteFieldQuadChar F x = ((Fintype.card F - 1 : ℕ) : ℤ)) := by
  constructor
  · intro hF
    simpa [finiteFieldQuadChar] using quadraticChar_sum_zero (F := F) hF
  · intro hF
    classical
    rw [← Finset.add_sum_erase _ (fun x => finiteFieldQuadChar F x)
      (Finset.mem_univ (0 : F))]
    have h0 : finiteFieldQuadChar F (0 : F) = 0 := quadraticChar_zero
    rw [h0, zero_add]
    have hpos : ∀ x ∈ (Finset.univ.erase (0 : F)), finiteFieldQuadChar F x = 1 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      simpa [finiteFieldQuadChar] using quadraticChar_eq_one_of_char_two (F := F) hF hx.1
    rw [Finset.sum_congr rfl hpos]
    have hcard : (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

end Qatlib.Papers.QuadChar00.MainResults
