/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpaceCompiler
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensionsDefs

/-!
# Resource ledgers for query-space compilation

`compiledLedger` records the forward accesses, address width, per-access fees, and fixed gates
of a compiled query-space circuit. The module calculates its exact charge, verifies the absence
of controlled and inverse accesses, and counts the dimension of the reference extension.

The ledger distinguishes oracle queries from fixed gates in the standard quantum circuit model
of [NielsenChuang2010].

## Main statements

* `compiledLedger_exact`: exact access and gate accounting
* `compiledLedger_no_extra_capability`: honesty without controlled or inverse capabilities
* `reference_space_cardinality`: cardinality of the reference extension

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CompressedQuery.CompressOracle
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
variable {a : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The access ledger for `compileCircuit`, recording its forward queries, address width,
per-access charge, and fixed gates. -/
def compiledLedger (c : Bool) (C : Circuit (Data (Reg a) W)) (perAccess : ℕ) : AccessLedger where
  forwardAccesses := QueryCount (compileCircuit c C)
  controlledAccesses := 0
  inverseAccesses := 0
  addressBits := a
  perAccessCharge := perAccess
  fixedGates := GateCount (compileCircuit c C)

/-- The compiled ledger preserves the query count, adds five fixed gates per query, and charges
`QueryCount C * (a + perAccess)`, with no controlled or inverse accesses. -/
theorem compiledLedger_exact (c : Bool) (C : Circuit (Data (Reg a) W)) (perAccess : ℕ) :
    let L := compiledLedger c C perAccess
    L.forwardAccesses = QueryCount C ∧ L.controlledAccesses = 0 ∧ L.inverseAccesses = 0 ∧
      L.addressBits = a ∧ L.perAccessCharge = perAccess ∧
      L.fixedGates = GateCount C + 5 * QueryCount C ∧
      L.accessCharge = QueryCount C * (a + perAccess) := by
  simp [compiledLedger, compile_queries, compile_gates, AccessLedger.accessCharge,
    AccessLedger.totalAccesses]

/-- The compiled ledger has no controlled or inverse accesses and satisfies capability honesty
when neither capability is granted. -/
theorem compiledLedger_no_extra_capability (c : Bool)
    (C : Circuit (Data (Reg a) W)) (perAccess : ℕ) :
    (compiledLedger c C perAccess).freeOfControlInverse ∧
      controlInverseHonest (compiledLedger c C perAccess) False False := by
  simp [compiledLedger, AccessLedger.freeOfControlInverse, controlInverseHonest]

/-- A circuit with at least one query has strictly positive compiled access charge when its
address and per-access fee sum is positive. -/
theorem compiledLedger_positive_charge (c : Bool)
    (C : Circuit (Data (Reg a) W)) (perAccess : ℕ)
    (hq : 0 < QueryCount C) (hfee : 0 < a + perAccess) :
    0 < (compiledLedger c C perAccess).accessCharge := by
  rw [(compiledLedger_exact c C perAccess).2.2.2.2.2.2]
  exact Nat.mul_pos hq hfee

/-- The full reference space has cardinality equal to the data-space cardinality times the
reference index cardinality. -/
theorem reference_space_cardinality (I W : Type) [Fintype I] [Fintype W] :
    Fintype.card (Full I W) = Fintype.card (Data I W) * Fintype.card I :=
  Fintype.card_prod _ _

end
end Qatlib.Concepts.StoppingCore.InterruptBridge
