/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Concepts.QPrograms.MeasureProg
public import Qatlib.Concepts.QPrograms.QueryBilling
public import Qatlib.Concepts.CostModels.UnitAlgebra

@[expose] public section

/-!
# Bridging the XOR oracle into program semantics and billing

This module connects between the word layer and the program layer of the toolkit. The
standard XOR oracle is a legal oracle matrix for word denotation, so a unitary query
word over it denotes a unitary matrix; the word's public query count and the program
layer's history billing agree on one query step; and conditioning on a positive-weight
history remains available for policies over such oracles through the existing
`MeasureProg` layer, which this module only references.

## Main statements

* `xorWord_uni`: unitary words over the XOR oracle denote unitary matrices.
* `oneQueryAgree`: one query step counts one query and bills one oracle call.
* `wordQueryCount`: the word profile's query field is the public `QueryCount`.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.CountBridge
open Qatlib.Concepts.QPrograms.QueryBilling
open Qatlib.Concepts.CostModels.UnitAlgebra

namespace Qatlib.Concepts.QPrograms.OracleBridge

variable {a w : ℕ}

/-- A unitary query word over the standard XOR oracle denotes a unitary matrix:
the standard XOR oracle plugs into the word semantics without new assumptions. -/
theorem xorWord_uni (f : Addr a → Bool) {C : Circuit (OReg a w)}
    (hC : IsUnitaryCircuit C) :
    Denote (xorOracle f) C ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  denote_unitary _ (xorOracle_uni f) hC

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- Under the constant unit cost, one billed history step charges exactly one unit. -/
theorem oneCallBills (o : OReg a w) :
    progQCost (fun _ => 1) [o] = 1 := by
  show (1 : ℕ) + charge (fun _ => 1) [o] [] = 1
  rfl

/-- The word and program layers agree on a single query step: the public counter
counts one query and the constant-unit history billing charges one unit; the bridge
is a bookkeeping agreement, not an identification of the two semantics. -/
theorem oneQueryAgree (o : OReg a w) :
    QueryCount (I := OReg a w) [Step.query] = progQCost (fun _ => 1) [o] := by
  simp only [QueryCount, progQCost, charge]

/-- The query field of a word profile is the public query counter: word profiles and
the public counter never disagree. -/
theorem wordQueryCount {I : Type*} (C : Circuit I) :
    (wordProfile C).queries = some (QueryCount C) :=
  wordProfileQ C

end Qatlib.Concepts.QPrograms.OracleBridge
