/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem8CorrectedStat

/-!
# Corrected multiple-target quantum query lower bound

Proves `theorem8Corrected` using the family hybrid bound and subset-incidence budget. The
conclusion `Theorem8Corrected` retains natural-number division inside the square root before
taking the integer floor. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `theorem8Corrected`: Establishes `Theorem8Corrected`, the floor query lower bound for
  fixed-cardinality marked subsets with average success at least one half.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

/-- Establishes `Theorem8Corrected`, the floor query lower bound for fixed-cardinality marked
subsets with average success at least one half. See [BoyerEtAl1998]. -/
theorem theorem8Corrected : Theorem8Corrected.{u, v} := by
  intro C Y _ _ _ _ t ht htN U V f ψ hψ r hagree hsuccess
  let J := MarkedSubsets Y t
  let c : ℝ := ((Fintype.card Y - 1).choose (t - 1) : ℕ)
  let m : ℕ := Fintype.card Y / t
  have hJ : 0 < Fintype.card J := by
    dsimp [J]
    rw [markedSubsets_card]
    exact Nat.choose_pos htN
  letI : Nonempty J := Fintype.card_pos_iff.mp hJ
  have hbudget : (m : ℝ) * c ≤ Fintype.card J := by
    dsimp [m, c, J]
    rw [markedSubsets_card]
    exact_mod_cast subset_overlap_budget (Fintype.card Y) t ht htN
  have hmass (n : ℕ) (_hn : n ≤ r) :
      (∑ B : J, ‖QueryProjection (SubsetQuerySet (f n) B.val) (UnitaryEvolution U ψ n)‖ ^ 2) ≤ c := by
    have h := subset_query_mass t ht (f n) (UnitaryEvolution U ψ n)
    rw [unitaryEvolution_norm, hψ, one_pow, mul_one] at h
    exact h
  apply floor_bound_of_quadratic m r
  · exact family_fixed_query_quadratic U V (fun n B => SubsetQuerySet (f n) B.val)
      ψ hψ r m c hbudget hagree hmass hsuccess
  · intro hr
    subst r
    have hsmall : (Fintype.card J : ℝ) / 2 ≤ c := hsuccess.trans (hmass 0 le_rfl)
    have hm := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    have hJr : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
    have hmle : (m : ℝ) ≤ 2 := by
      apply (mul_le_mul_iff_of_pos_right hJr).mp
      nlinarith only [hm, hbudget]
    exact_mod_cast hmle

end Qatlib.Concepts.SearchStopping.QueryLowerBound
