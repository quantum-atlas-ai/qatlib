/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.MessagingBounds.CollapsedMessageGuessingStat

/-!
# A decoding advantage for collapsed Bell messages

`collapsedMessageGuessing` proves that a noninjective encoding with at least two distinct
message values permits recovery of a uniform Bell outcome with probability greater than one
quarter. The result concerns decoding after the encoded message is available. The communication
setting is teleportation [BennettEtAl1993Teleportation]; see also [Wilde2017] for the
information-theoretic background.

## Main statements

* `collapsedMessageGuessing`: A noninjective, nonconstant encoding of Bell outcomes has a
  decoder whose uniform recovery probability is strictly greater than `1 / 4`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QuditTeleport.MessagingBounds
open scoped Classical

/-- A noninjective, nonconstant encoding of Bell outcomes has a decoder whose uniform recovery
probability is strictly greater than `1 / 4`. -/
theorem collapsedMessageGuessing : CollapsedMessageGuessing := by
  intro κ _ _ m _ hnontrivial
  obtain ⟨a,b,hm⟩ := hnontrivial
  have hab : a ≠ b := fun h => hm (congrArg m h)
  let g : κ → Bool × Bool := fun v => if v=m a then a else b
  have ha : g (m a)=a := by simp [g]
  have hb : g (m b)=b := by simp [g,Ne.symm hm]
  have hs : {a,b} ⊆ Finset.univ.filter (fun o => g (m o)=o) := by
    intro o ho
    simp only [Finset.mem_insert,Finset.mem_singleton] at ho
    rcases ho with rfl | rfl <;> simp [ha,hb]
  have hc := Finset.card_le_card hs
  rw [Finset.card_pair hab] at hc
  have hc' : (2 : ℝ) ≤ ((Finset.univ.filter (fun o => g (m o)=o)).card : ℝ) := by
    exact_mod_cast hc
  refine ⟨g,?_⟩
  linarith

end Qatlib.Concepts.QuditTeleport.MessagingBounds
