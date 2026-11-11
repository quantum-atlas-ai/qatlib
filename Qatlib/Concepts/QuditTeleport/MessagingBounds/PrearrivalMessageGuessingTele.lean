/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingStat
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith

/-!
# A prearrival Bell-message guessing bound

`prearrivalMessageGuessing` proves that collapsing any pair of the four Bell outcomes produces a
message value with probability at least one half under the uniform outcome law. The
communication setting is teleportation [BennettEtAl1993Teleportation]; see also [Wilde2017] for
the information-theoretic background.

## Main statements

* `prearrivalMessageGuessing`: A noninjective Bell-outcome encoding has a message value of
  probability at least `1 / 2`, strictly exceeding `1 / 4`. See the communication argument in
  [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.MessagingBounds

/-- A noninjective Bell-outcome encoding has a message value of probability at least `1 / 2`,
strictly exceeding `1 / 4`. See the communication argument in
[BennettEtAl1993Teleportation]. -/
theorem prearrivalMessageGuessing : PrearrivalMessageGuessing := by
  classical
  intro κ _ _ m hm
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hm
  have hs : {a, b} ⊆ Finset.univ.filter (fun o => m o = m a) := by
    intro o ho
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl
    · simp
    · simp [hab]
  have hc := Finset.card_le_card hs
  rw [Finset.card_pair hne] at hc
  have hc' : (2 : ℝ) ≤ ((Finset.univ.filter (fun o => m o = m a)).card : ℝ) := by
    exact_mod_cast hc
  refine ⟨m a, ?_, ?_⟩ <;> linarith

end Qatlib.Concepts.QuditTeleport.MessagingBounds
