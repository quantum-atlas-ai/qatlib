/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.AdaptiveFiniteTape

/-!
# Counting finite events by fibers

This module supplies exact cardinality identities for events on finite function and product
spaces. `function_coordinate_event_card` isolates one tape coordinate, while
`product_event_card_bound` lifts a uniform bound on product fibers to a bound on the whole
event. For background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `function_coordinate_event_card`: The number of functions whose value at `a` satisfies `P`
  equals the number of values satisfying `P` times the number of functions on the remaining
  coordinates.
* `product_event_card_bound`: If every fiber count times `R` is at most `C * Fintype.card X`,
  the full product event count times `R` is at most `C * Fintype.card (A × X)`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- The number of functions whose value at `a` satisfies `P` equals the number of values
satisfying `P` times the number of functions on the remaining coordinates. -/
theorem function_coordinate_event_card {A X : Type} [Fintype A] [DecidableEq A] [Fintype X]
    (a : A) (P : X→Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : A→X=>P (t a))).card=
      (Finset.univ.filter P).card*Fintype.card ({b : A // b≠a}→X) := by
  rw [function_event_card_split a]
  have he : ∀ x : X,Finset.univ.filter (fun r : {b : A // b≠a}→X=>P (extendCoordinate a x r a))=
      if P x then Finset.univ else ∅ := by
    intro x
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,extendCoordinate_self]
    split_ifs with hx <;> simp [hx]
  simp only [he]
  have hc : ∀ x : X,(if P x then (Finset.univ : Finset ({b : A // b≠a}→X)) else ∅).card=
      if P x then Fintype.card ({b : A // b≠a}→X) else 0 := by
    intro x
    split_ifs <;> simp
  simp only [hc,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]

/-- The number of pairs satisfying `P` is the sum, over first coordinates, of the counts
satisfying the corresponding fiber predicate. -/
theorem product_event_card_fibers {A X : Type} [Fintype A] [Fintype X]
    (P : A→X→Prop) :
    (Finset.univ.filter (fun z : A×X=>P z.1 z.2)).card=∑ a : A,(Finset.univ.filter (P a)).card := by
  calc
    _ = ∑ z : A×X,if P z.1 z.2 then (1:ℕ) else 0 := by simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]

/-- If every fiber count times `R` is at most `C * Fintype.card X`, the full product event count
times `R` is at most `C * Fintype.card (A × X)`. -/
theorem product_event_card_bound {A X : Type} [Fintype A] [Fintype X]
    (P : A→X→Prop) (R C : ℕ)
    (h : ∀ a,(Finset.univ.filter (P a)).card*R≤C*Fintype.card X) :
    (Finset.univ.filter (fun z : A×X=>P z.1 z.2)).card*R≤C*Fintype.card (A×X) := by
  rw [product_event_card_fibers,Finset.sum_mul]
  apply (Finset.sum_le_sum (fun a _=>h a)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_id]
  ring
end Qatlib.Concepts.WalkSearch.MainResults
