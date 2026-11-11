/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Cancellation of noncrossing components (Lemma 3.1)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 3.1, page 14.

The activation comparison expands a product operator in the Möbius basis indexed
by subsets of the active occurrence labels.  A subset `F` whose induced graph has
a connected component touching neither the source set `S` nor the cut set `C`
contributes the alternating sum

`∑_{T ⊆ F} (-1)^{|T|}`

because the component can be independently switched on and off without changing
the remaining connectivity pattern.  Since that alternating sum over the
powerset of a nonempty set is zero, the whole contribution `Δ_F M` vanishes.

We formalize the combinatorial core: the Möbius alternating sum over the
powerset of any nonempty finite set is zero.  This is the exact cancellation
used in the source, and it is an operator identity because the coefficients are
scalars multiplying the fixed matrix products.
-/

open Finset

namespace Qatlib.Papers.ShallowLind26.ShallowSim.Cancellation

set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

/-- The alternating (Möbius) sum over the powerset of `insert a s` vanishes. -/
theorem alternating_powerset_insert (a : α) (s : Finset α) (ha : a ∉ s) :
    ∑ T ∈ (insert a s).powerset, (-1 : ℤ) ^ T.card = 0 := by
  rw [Finset.sum_powerset_insert ha]
  have hneg : ∑ t ∈ s.powerset, (-1 : ℤ) ^ (insert a t).card
      = - ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
    rw [Finset.card_insert_of_notMem hat, pow_succ]
    ring
  rw [hneg]
  ring

/-- **Lemma 3.1, Möbius cancellation.**  If the set of active labels is
nonempty, its alternating powerset sum is zero. -/
theorem alternating_powerset_sum (F : Finset α) (hF : F.Nonempty) :
    ∑ T ∈ F.powerset, (-1 : ℤ) ^ T.card = 0 := by
  obtain ⟨a, ha⟩ := hF
  have h : insert a (F.erase a) = F := Finset.insert_erase ha
  rw [← h]
  exact alternating_powerset_insert a (F.erase a) (Finset.notMem_erase a F)

/-- The cancellation also holds for the signed sum with a fixed external
weight: a nonempty component contributes zero times any coefficient. -/
theorem alternating_weighted_sum (F : Finset α) (hF : F.Nonempty) (w : ℤ) :
    w * (∑ T ∈ F.powerset, (-1 : ℤ) ^ T.card) = 0 := by
  rw [alternating_powerset_sum F hF, mul_zero]

end Qatlib.Papers.ShallowLind26.ShallowSim.Cancellation
