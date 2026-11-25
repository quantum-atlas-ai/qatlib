/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ModularFunct00.MainResults.Approximation.Theorem21

@[expose] public section

/-!
# Word length of concatenated gate approximants

The error allocation in the proof of [FreedmanLarsenWang2000], Theorem 2.3,
uses inverse accuracy `10 * n`. Given a quadratic bound on each word at
this accuracy, the concatenated word has the following cubic length budget.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ModularFunct00.MainResults

open Qatlib.Papers.ModularFunct00.MainResults
open Qatlib.Papers.ModularFunct00.MainResults.Approximation

/-- Concatenating the specified gate approximants multiplies their uniform length bound by the
number of gates. -/
theorem braid_budget {G : Type*} [Group G] {m n C : ℕ} {σ : Fin m → G} {bs : List G}
    (hlen : bs.length = n) (hbs : ∀ b ∈ bs, BraidWord σ (C * (10 * n) ^ 2) b) :
    BraidWord σ (C * (10 * n) ^ 2 * n) bs.prod := by
  simpa only [hlen, Nat.mul_comm n] using theorem2_1_word_length_budget hbs

end Qatlib.Papers.ModularFunct00.MainResults
