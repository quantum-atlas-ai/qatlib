/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Message counts for no-signalling codes

For a nonnegative array with a normalized reference input and an input-independent receiver
marginal, `no_signalling_total_success_le_messages` bounds the total diagonal success weight by
the message alphabet size. Exact decoding then bounds the input alphabet size by the number of
messages. These bounds formalize the no-signalling communication argument for teleportation
[BennettEtAl1993Teleportation].

## Main statements

* `no_signalling_total_success_le_messages`: Under nonnegativity, reference normalization, and
  the stated no-signalling marginal identity, the total diagonal success weight is at most
  `Fintype.card M`.
* `no_signalling_exact_code_card_le`: A code satisfying the stated nonnegativity, normalization,
  and no-signalling conditions with unit success for every input has `Fintype.card X ≤
  Fintype.card M`.
* `no_signalling_small_alphabet_fails`: If the message alphabet is smaller than the input
  alphabet, the stated no-signalling conditions force some input to have success weight strictly
  less than one.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.NoSignalCode

open scoped BigOperators

/-- Under nonnegativity, reference normalization, and the stated no-signalling marginal
identity, the total diagonal success weight is at most `Fintype.card M`. -/
theorem no_signalling_total_success_le_messages
    {X M : Type} [Fintype X] [Fintype M] (x₀ : X)
    (p : X → M → M → X → ℝ)
    (hpos : ∀ x s m y, 0 ≤ p x s m y)
    (hnorm : ∀ s, ∑ m, ∑ y, p x₀ s m y = 1)
    (hns : ∀ x s y, ∑ m, p x s m y = ∑ m, p x₀ s m y) :
    (∑ x, ∑ m, p x m m x) ≤ (Fintype.card M : ℝ) := by
  classical
  calc
    (∑ x, ∑ m, p x m m x) ≤ ∑ x, ∑ m, ∑ a, p x m a x := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro m _
      exact Finset.single_le_sum (fun a _ => hpos x m a x) (Finset.mem_univ m)
    _ = ∑ x, ∑ m, ∑ a, p x₀ m a x := by simp_rw [hns]
    _ = ∑ m, ∑ x, ∑ a, p x₀ m a x := Finset.sum_comm
    _ = ∑ m, ∑ a, ∑ x, p x₀ m a x := by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_comm
    _ = ∑ _m : M, (1 : ℝ) := by simp_rw [hnorm]
    _ = (Fintype.card M : ℝ) := by simp

/-- A code satisfying the stated nonnegativity, normalization, and no-signalling conditions with
unit success for every input has `Fintype.card X ≤ Fintype.card M`. -/
theorem no_signalling_exact_code_card_le
    {X M : Type} [Fintype X] [Fintype M] (x₀ : X)
    (p : X → M → M → X → ℝ)
    (hpos : ∀ x s m y, 0 ≤ p x s m y)
    (hnorm : ∀ s, ∑ m, ∑ y, p x₀ s m y = 1)
    (hns : ∀ x s y, ∑ m, p x s m y = ∑ m, p x₀ s m y)
    (hexact : ∀ x, ∑ m, p x m m x = 1) :
    Fintype.card X ≤ Fintype.card M := by
  have h := no_signalling_total_success_le_messages x₀ p hpos hnorm hns
  simp_rw [hexact] at h
  simpa using h

/-- If the message alphabet is smaller than the input alphabet, the stated no-signalling
conditions force some input to have success weight strictly less than one. -/
theorem no_signalling_small_alphabet_fails
    {X M : Type} [Fintype X] [Fintype M] (x₀ : X)
    (p : X → M → M → X → ℝ)
    (hpos : ∀ x s m y, 0 ≤ p x s m y)
    (hnorm : ∀ s, ∑ m, ∑ y, p x₀ s m y = 1)
    (hns : ∀ x s y, ∑ m, p x s m y = ∑ m, p x₀ s m y)
    (hsmall : Fintype.card M < Fintype.card X) :
    ∃ x, ∑ m, p x m m x < 1 := by
  classical
  by_contra h
  push Not at h
  have hlower : (Fintype.card X : ℝ) ≤ ∑ x, ∑ m, p x m m x := by
    calc
      (Fintype.card X : ℝ) = ∑ _x : X, (1 : ℝ) := by simp
      _ ≤ ∑ x, ∑ m, p x m m x := Finset.sum_le_sum (fun x _ => h x)
  have hle := hlower.trans (no_signalling_total_success_le_messages x₀ p hpos hnorm hns)
  have hsmall' : (Fintype.card M : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hsmall
  linarith

end Qatlib.Concepts.QuditTeleport.NoSignalCode
