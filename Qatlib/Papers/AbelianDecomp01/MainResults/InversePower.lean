/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# Inversion from a known positive order

After Corollary 8 the paper uses the order of an element to implement
the inverse group action during uncomputation. Its predecessor power
cancels the element on either side.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AbelianDecomp01.MainResults

/-- If the known order is positive, raising the element to the
predecessor of its order produces a two-sided inverse. -/
theorem inverse_power_of_order {G : Type*} [Group G] (a : G) {r : ℕ}
    (hr : orderOf a = r) (hpos : 0 < r) :
    a ^ (r - 1) * a = 1 ∧ a * a ^ (r - 1) = 1 := by
  have hpow : a ^ (r - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel hpos, ← hr, pow_orderOf_eq_one]
  exact ⟨by simpa only [pow_succ] using hpow, by simpa only [pow_succ'] using hpow⟩

end Qatlib.Papers.AbelianDecomp01.MainResults
