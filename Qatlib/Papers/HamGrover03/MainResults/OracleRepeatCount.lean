/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamGrover03.MainResults.MainRotation

@[expose] public section

/-!
# Repeated oracle Hamiltonian steps

Counts the oracle queries of the repeated oracle subcircuit from [RolandCerf2003], Section IV.
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.HamGrover03.MainResults

namespace Qatlib.Papers.HamGrover03.MainResults

/-- Repeating the oracle Hamiltonian step `R` times uses exactly `2 * R` oracle queries. -/
theorem query_count_repeat_oracle_ham_step {I : Type} [Fintype I] [DecidableEq I]
    (t : ℝ) (R : ℕ) : QueryCount (RepeatCircuit (oracleHamStepCircuit (I := I) t) R) = 2 * R := by
  rw [queryCount_repeatCircuit, queryCount_oracleHamStepCircuit, Nat.mul_comm]

end Qatlib.Papers.HamGrover03.MainResults
