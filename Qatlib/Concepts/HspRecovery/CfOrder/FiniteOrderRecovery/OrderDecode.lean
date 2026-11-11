/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Max

/-!
# Minimum candidates for finite order decoding

Expresses power tests in a finite group as divisibility by the element order. The set
`d2bCandSet` contains bounded positive multiples of a proposed order that are also multiples of
some supplied denominator.

Characterizes when the minimum of this set is the proposed order, giving a divisibility
criterion for the order postprocessing considered in [Shor1997].

## Main statements

* `pow_eq_one_iff_orderOf_dvd`: rewrites a power test as divisibility.
* `d2bCandSet_min`: characterizes the minimum of the candidate set.
* `d2b_min_char`: specializes the characterization to a group element's order.

## References

* [Shor, 1997][Shor1997]
-/

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery

open Finset

/-- For an element of a finite group, `u ^ x = 1` exactly when `orderOf u` divides `x`. -/
theorem pow_eq_one_iff_orderOf_dvd {G : Type*} [Group G] [Fintype G] (u : G)
    (x : ℕ) : u ^ x = 1 ↔ orderOf u ∣ x :=
  (orderOf_dvd_iff_pow_eq_one).symm

/-- The positive naturals below `bound` that are multiples of `r` and of at least one element of
`ds`. -/
def d2bCandSet (r : ℕ) (ds : List ℕ) (bound : ℕ) : Finset ℕ :=
  (Finset.range bound).filter (fun y => 0 < y ∧ r ∣ y ∧ ds.any (fun d => d ∣ y))

/-- For positive `r < bound` and a nonempty candidate set, the minimum equals `r` exactly when
some element of `ds` divides `r`. -/
theorem d2bCandSet_min (r : ℕ) (ds : List ℕ) (bound : ℕ)
    (hr : 0 < r) (hrb : r < bound) (hne : (d2bCandSet r ds bound).Nonempty) :
    (d2bCandSet r ds bound).min' hne = r ↔ ∃ d ∈ ds, d ∣ r := by
  constructor
  · intro hmin
    have h0 : (d2bCandSet r ds bound).min' hne ∈ d2bCandSet r ds bound :=
      min'_mem _ hne
    rw [hmin] at h0
    simp only [d2bCandSet, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq,
      List.any_eq_true] at h0
    obtain ⟨-, -, -, d, hd, hdr⟩ := h0
    exact ⟨d, hd, hdr⟩
  · intro ⟨d, hd, hdr⟩
    have hrmem : r ∈ d2bCandSet r ds bound := by
      simp only [d2bCandSet, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq,
        List.any_eq_true]
      exact ⟨hrb, hr, Nat.dvd_refl r, d, hd, hdr⟩
    have hall : ∀ y ∈ d2bCandSet r ds bound, r ≤ y := by
      intro y hy
      simp only [d2bCandSet, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨-, hy0, hrd, -⟩ := hy
      exact Nat.le_of_dvd hy0 hrd
    exact le_antisymm (min'_le _ r hrmem) (le_min' _ hne r hall)

/-- For a positive element order below `bound` and a nonempty candidate set, its minimum is the
order exactly when some element of `ds` divides the order. -/
theorem d2b_min_char {G : Type*} [Group G] [Fintype G] (u : G) (ds : List ℕ)
    (bound : ℕ) (h0 : 0 < orderOf u) (hb : orderOf u < bound)
    (hne : (d2bCandSet (orderOf u) ds bound).Nonempty) :
    (d2bCandSet (orderOf u) ds bound).min' hne = orderOf u
      ↔ ∃ d ∈ ds, d ∣ orderOf u :=
  d2bCandSet_min _ _ _ h0 hb hne

end Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery
