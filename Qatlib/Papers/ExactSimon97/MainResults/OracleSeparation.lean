/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.ClassicalLowerBound
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

abbrev OracleFamily : Type := (n : ℕ) → BoolVec n → BoolVec (n - 1)

abbrev DecisionProblem : Type := ℕ → Bool

theorem assemble_scale_choices
    (P : (n : ℕ) → (BoolVec n → BoolVec (n - 1)) → Prop)
    (h : ∀ n, 4 ≤ n → ∃ ρ, P n ρ) :
    ∃ O : OracleFamily, ∀ n, 4 ≤ n → P n (O n) := by
  classical
  refine ⟨fun n => if hn : 4 ≤ n then Classical.choose (h n hn) else 0, ?_⟩
  intro n hn
  have hspec := Classical.choose_spec (h n hn)
  simpa only [dif_pos hn] using hspec

end Qatlib.Papers.ExactSimon97.MainResults
