/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalTigh
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit

/-!
# Prepared circuits for amplified Haar pairs

This module defines marked pairs, translates ordinary circuit steps to prepared steps, and
constructs `aqHaarPairWord` and its output state. The circuit combines amplitude amplification,
an input phase query, and a Boolean Hadamard for the amplified Haar-transform method of
[Cornwell2014].

## Main statements

* `aqHaarPairMarked`: The finite set of pairs whose first coordinate belongs to E, with either
  Boolean orientation.
* `aqHaarPairWord`: The prepared-step word for j amplification rounds, an input phase query, and
  a Hadamard on the Boolean orientation register.
* `aqHaarPairOutput`: The state obtained by evaluating `aqHaarPairWord` with marked-pair and
  input phase oracles on the preparation seed.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.GateCore

set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.SearchStopping.GateCore Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The finite set of pairs whose first coordinate belongs to E, with either Boolean
orientation. -/
def aqHaarPairMarked (E : Finset I) : Finset (I × Bool) :=
  Finset.univ.filter fun z => z.1 ∈ E

/-- Translates a fixed gate to the same prepared gate and an oracle query to a forward data
query. -/
noncomputable def aqHaarPreparedOfStep : Step (I × Bool) → PreparedStep (I × Bool)
  | .gate U => .gate U
  | .query => .dataForward

/-- The prepared-step word for j amplification rounds, an input phase query, and a Hadamard on
the Boolean orientation register. -/
noncomputable def aqHaarPairWord (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool) (j : ℕ) : List (PreparedStep (I × Bool)) :=
  [.gate (TensorGate (1 : Matrix I I ℂ) Hadamard), .prepareForward] ++
    ((SourceGateCircuit T' (Ket seed) j).reverse.map aqHaarPreparedOfStep) ++
    [.gate T']

/-- The state obtained by evaluating `aqHaarPairWord` with marked-pair and input phase oracles
on the preparation seed. -/
noncomputable def aqHaarPairOutput (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool) (j : ℕ) (E : Finset I) (S : I × Bool → Bool) : QState (I × Bool) :=
  evaluatePrepared (PhaseOracle (fun z => decide (z.1 ∈ E))) (PhaseOracle S)
    (aqHaarPairWord T' seed j) *ᵥ Ket seed

end Qatlib.Concepts.AmpTransform.HaarPairTest
