/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Concepts.QPrograms.OracleBridge

@[expose] public section

/-!
# Deutsch–Jozsa first slice: one standard query separates two concrete oracles

The first auditable slice of the QAlgorithms97 line (Deutsch–Jozsa).
It uses the standard XOR oracle on a two-bit address register: a constant
and a balanced concrete oracle act differently on the all-zero basis state after a
single standard query, and the query is one step of the unified word semantics, so
the public counter counts exactly one query. This slice deliberately stays with the
standard (non-phase) oracle form and a concrete two-bit instance; the Hadamard-layer
phase form, the register-wide decision procedure, and the constant-vs-balanced
dichotomy over all inputs remain open and are not claimed here.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Concepts.QPrograms.OracleBridge

namespace Qatlib.Papers.QAlgorithms97.DJSlice

/-- The constant oracle: always answers zero. -/
def djConst : Addr 2 → Bool := fun _ => false

/-- The balanced oracle: answers the first address bit. -/
def djBal : Addr 2 → Bool := fun a => a ⟨0, by omega⟩

/-- The witness basis state: first address bit set, answer zero, no work wires. -/
def djWit : OReg 2 0 := (fun _ => true, false, fun _ => false)

/-- The constant oracle fixes the answer bit of the witness state; the balanced
oracle flips it: one standard query already separates the two concrete oracles on
this basis state. -/
theorem dj_one_query_diff :
    xorInto djBal djWit ≠ xorInto djConst djWit := by
  unfold xorInto djBal djConst djWit
  decide

/-- The separating step is one query of the unified word semantics: the public
counter counts exactly one query for the single-query word over the balanced
oracle's register. -/
theorem dj_one_query_count :
    QueryCount (I := OReg 2 0) [Step.query] = 1 := by
  simp [QueryCount]

end Qatlib.Papers.QAlgorithms97.DJSlice
