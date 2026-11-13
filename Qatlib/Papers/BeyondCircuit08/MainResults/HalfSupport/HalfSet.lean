/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport.TwoLevelElim

/-!
# Choosing half-size coordinate supports

For `m ≥ 4`, `exists_halfSet` places any two distinct coordinate indices in a set of size `m /
2`. Combining this choice with two-level elimination gives a unitary supported on such a set
that clears a selected matrix entry, as needed in the half-support construction of [Jordan2008].

## Main statements

* `exists_halfSet`: a half-size coordinate set containing two specified distinct indices exists.
* `exists_halfSupport_kill_entry_uncond`: if the two selected column entries are not both zero,
  a unitary on a half-size support clears the second one.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

variable {m : ℕ}

/-- For `m ≥ 4`, any two distinct indices in `Fin m` belong to a finite set of cardinality `m /
2` [Jordan2008]. -/
theorem exists_halfSet (hm : 4 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ∃ S : Finset (Fin m), S.card = m / 2 ∧ i ∈ S ∧ j ∈ S := by
  have hpos : 2 ≤ m / 2 := by omega
  have hpair : ({i, j} : Finset (Fin m)).card = 2 := by
    simp [hij]
  have hle : m / 2 - 2 ≤ ((Finset.univ : Finset (Fin m)) \ {i, j}).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hpair,
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m)) \ {i, j})
      (n := m / 2 - 2) hle
  refine ⟨{i, j} ∪ t, ?_, by simp, by simp⟩
  have hdisj : Disjoint ({i, j} : Finset (Fin m)) t := by
    rw [Finset.disjoint_left]
    intro x hx hxt
    exact (Finset.mem_sdiff.mp (ht_sub hxt)).2 hx
  rw [Finset.card_union_of_disjoint hdisj, hpair, ht_card]
  omega

/-- For `m ≥ 4`, two distinct rows with column entries not both zero determine a unitary fixing
the complement of some set of size `m / 2` whose left action clears the second selected
entry [Jordan2008]. -/
theorem exists_halfSupport_kill_entry_uncond (U : Matrix (Fin m) (Fin m) ℂ)
    (hm : 4 ≤ m) {i j : Fin m} (hij : i ≠ j) {k : Fin m}
    (hne : U i k ≠ 0 ∨ U j k ≠ 0) :
    ∃ (S : Finset (Fin m)) (W : Matrix (Fin m) (Fin m) ℂ),
      S.card = m / 2 ∧ FixesComplement S W ∧ (W * U) j k = 0 := by
  obtain ⟨S, hcard, hi, hj⟩ := exists_halfSet hm hij
  obtain ⟨W, hfix, hzero⟩ := exists_halfSupport_kill_entry U hij hi hj hne
  exact ⟨S, W, hcard, hfix, hzero⟩

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
