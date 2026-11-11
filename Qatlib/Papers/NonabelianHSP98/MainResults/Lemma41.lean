/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup

/-!
# Decomposition of wreath-product subgroups

This module proves `lemma_4_1`, which expresses a wreath-product subgroup as the join of its
intersection with the base subgroup and its intersection with its swapped image. A binary
residue-class dichotomy supports the proof. This development accompanies [RoettelerBeth1998].

## Main statements

* `ZMod2_eq_zero_or_one`: every binary residue is zero or one.
* `lemma_4_1`: the subgroup decomposition by the base and swapped intersection.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Lemma41

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath

variable {n : ℕ}

/-- Every element of `ZMod 2` is either zero or one. -/
lemma ZMod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

/-- A wreath-product subgroup is the join of its intersection with the base subgroup and its
intersection with its swapped image. This is Lemma 4.1 of [RoettelerBeth1998]. -/
theorem lemma_4_1 (U : Subgroup (Wreath n)) :
    U = (U ⊓ base n) ⊔ (U ⊓ conjSub U) := by
  apply le_antisymm
  · intro u hu
    by_cases ha : u.a = 0
    · exact Subgroup.mem_sup_left (show u ∈ U ⊓ base n from ⟨hu, ha⟩)
    · have ha1 : u.a = 1 := by
        rcases ZMod2_eq_zero_or_one u.a with h | h
        · exact absurd h ha
        · exact h

      have hcube : u * u * u = swapFun u := cube_of_a_one ha1
      have hmemU : u * u * u ∈ U := U.mul_mem (U.mul_mem hu hu) hu
      have hconj : u ∈ conjSub U := by
        rw [mem_conjSub]
        refine ⟨u * u * u, hmemU, ?_⟩
        rw [hcube, swapFun_swapFun]
      exact Subgroup.mem_sup_right (show u ∈ U ⊓ conjSub U from ⟨hu, hconj⟩)
  · exact sup_le inf_le_left inf_le_left

end Qatlib.Papers.NonabelianHSP98.MainResults.Lemma41
