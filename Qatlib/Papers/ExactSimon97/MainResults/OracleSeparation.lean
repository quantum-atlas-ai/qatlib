/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.ClassicalLowerBound

/-!
# Selecting an oracle family across input sizes

This module introduces families of binary oracles and Boolean decision problems. The choice
theorem `assemble_scale_choices` combines a qualifying oracle at each input size at least four
into a single oracle family. The development follows [BrassardHoyer1997].

## Main statements

* `OracleFamily`: specifies an oracle from `n` bits to `n - 1` bits at each scale.
* `assemble_scale_choices`: assembles scale-by-scale witnesses into a family.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

/-- A family assigning to each input length `n` an oracle from `BoolVec n` to `BoolVec (n - 1)`. -/
abbrev OracleFamily : Type := (n : ℕ) → BoolVec n → BoolVec (n - 1)

/-- A Boolean-valued decision problem on natural-number input lengths. -/
abbrev DecisionProblem : Type := ℕ → Bool

/-- If for every `n ≥ 4` there exists an oracle satisfying `P n`, there is a single oracle
family satisfying all these conditions. -/
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
