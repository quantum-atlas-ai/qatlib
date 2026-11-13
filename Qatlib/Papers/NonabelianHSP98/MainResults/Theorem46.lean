/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

/-!
# When orthogonal complements form subgroups

`IsSubgroupSet` expresses that a set is the carrier of a subgroup. Theorem 4.6 characterizes
this property for `perpSub U`: it holds exactly when `U` is fixed by `conjSub`. This development
accompanies [RoettelerBeth1998].

## Main statements

* `theorem_4_6_fwd`: swap invariance makes the complement a subgroup carrier.
* `theorem_4_6_bwd`: subgroup closure of the complement forces swap invariance.
* `theorem_4_6`: the equivalence of these conditions.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Theorem46

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
open Finset

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The predicate that a set is the underlying set of some subgroup of `Wreath n`. -/
def IsSubgroupSet (S : Set (Wreath n)) : Prop :=
  ∃ H : Subgroup (Wreath n), (H : Set (Wreath n)) = S

/-- If `U` is fixed by `conjSub`, then `perpSub U` is the carrier of a subgroup. This is the
forward implication of Theorem 4.6 of [RoettelerBeth1998]. -/
theorem theorem_4_6_fwd (U : Subgroup (Wreath n)) (h : conjSub U = U) :
    IsSubgroupSet (perpSub U) :=
  ⟨perpGroup U (balanced_of_conjSub_eq U h), rfl⟩

/-- If `perpSub U` is a subgroup carrier, then `U` is fixed by `conjSub`. This is the reverse
implication of Theorem 4.6 of [RoettelerBeth1998]. -/
theorem theorem_4_6_bwd (U : Subgroup (Wreath n)) (h : IsSubgroupSet (perpSub U)) :
    conjSub U = U := by
  obtain ⟨H, hH⟩ := h
  by_cases hU1 : ∃ g ∈ U, g.a = 1
  · exact conjSub_eq_of_balanced U (balanced_of_exists_a_one U hU1)
  · push_neg at hU1
    have hbase : ∀ g ∈ U, g.a = 0 := by
      intro g hg
      rcases zmod2_eq_zero_or_one g.a with h0 | h1
      · exact h0
      · exact absurd h1 (hU1 g hg)
    have ht : t n ∈ perpSub U := by
      rw [mem_perpSub]
      intro u hu
      rw [mu_one_zero (t n) u (by simp) (hbase u hu)]
      simp
    have htH : t n ∈ H := by
      show t n ∈ (H : Set (Wreath n))
      rw [hH]; exact ht
    have hHbal : ∀ g ∈ H, swapFun g ∈ H :=
      balanced_of_exists_a_one H ⟨t n, htH, by simp⟩
    have hSbal : ∀ s ∈ perpSub U, swapFun s ∈ perpSub U := by
      intro s hs
      have hsH : s ∈ H := by
        show s ∈ (H : Set (Wreath n))
        rw [hH]; exact hs
      have h' : swapFun s ∈ (H : Set (Wreath n)) := hHbal s hsH
      rwa [hH] at h'
    have hUbal : ∀ g ∈ (U : Set (Wreath n)), swapFun g ∈ (U : Set (Wreath n)) := by
      rw [← perpSub_perpSub U]
      exact perp_balanced hSbal
    exact conjSub_eq_of_balanced U hUbal

/-- A subgroup is fixed by `conjSub` if and only if its orthogonal-complement set is a subgroup
carrier. This is Theorem 4.6 of [RoettelerBeth1998]. -/
theorem theorem_4_6 (U : Subgroup (Wreath n)) :
    conjSub U = U ↔ IsSubgroupSet (perpSub U) :=
  ⟨theorem_4_6_fwd U, theorem_4_6_bwd U⟩

end Qatlib.Papers.NonabelianHSP98.MainResults.Theorem46
