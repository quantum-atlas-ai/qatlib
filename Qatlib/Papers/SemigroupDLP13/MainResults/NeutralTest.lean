/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SemigroupDLP13.MainResults.PeriodicSemigroup.SourceMainResults

@[expose] public section

/-!
# The idempotence test on the cyclic part

The source locates the neutral element by testing whether it squares to itself.
The neutral laws and the inverse of each periodic element suffice within the
cyclic part.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SemigroupDLP13.MainResults

open Qatlib.Papers.SemigroupDLP13.MainResults.PeriodicSemigroup

/-- The periodic neutral power squares to itself. -/
theorem neutral_sq {S : Type*} [Monoid S] {g : S} {l n t : ℕ}
    (hn : 0 < n) (hg : g ^ (l + n) = g ^ l) (ht : l < t * n) :
    g ^ (t * n) * g ^ (t * n) = g ^ (t * n) :=
  neutral_mul_left hg (neutral_mem hn hg ht)

/-- In the cyclic part, the neutral power is the only idempotent. -/
theorem neutral_test {S : Type*} [Monoid S] {g x : S} {l n t : ℕ}
    (hn : 0 < n) (hg : g ^ (l + n) = g ^ l) (ht : l < t * n)
    (hx : x ∈ cyclicPart g l n) : x * x = x ↔ x = g ^ (t * n) := by
  constructor
  · intro hxx
    obtain ⟨y, _, hxy, _⟩ := inv_mem hn hg ht hx
    simpa only [mul_assoc, hxy, neutral_mul_right hg hx] using
      congrArg (fun a => a * y) hxx
  · rintro rfl
    exact neutral_sq hn hg ht

end Qatlib.Papers.SemigroupDLP13.MainResults
